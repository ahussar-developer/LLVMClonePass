#include "llvm/Transforms/Utils/FunctionCloning.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Mangler.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/ProfDataUtils.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/BlockFrequency.h"
#include "llvm/Support/BranchProbability.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <cxxabi.h>
#include <unordered_set>
#include <string>
#include <map>

using namespace llvm;

std::string demangle(const std::string& mangledName) {
    int status = 0;
    char* demangled = abi::__cxa_demangle(mangledName.c_str(), nullptr, nullptr, &status);

    if (status == 0) {
        std::string demangledName(demangled);
        std::free(demangled);
        return demangledName;
    } else {
        // Demangling failed, return the original mangled name
        return mangledName;
    }
}

// TO DO: Some researh makes it seem like this is unneccessary
std::string mangle(const std::string& funcName, llvm::Module& M) {
    return funcName;
}

std::string CloneTheFunction(Module &M, std::string funcName){
  std::string clonedFuncName = funcName + "`";
  // Find the original function by name
  Function *OrigFunc = M.getFunction(funcName);
  if (!OrigFunc) {
    errs() << "Original function not found: " << funcName << "\n";
    return "";
  } else{
    //errs() << "Found Function: " << OrigFunc->getName() << "\n";
  }

  if (M.getNamedValue(clonedFuncName)) {
    errs() << "Cloned function name already exists in the module. ABORT!\n";
    return "";
  }
  
  /*
  Function * 	llvm::CloneFunction (Function *F, ValueToValueMapTy &VMap, ClonedCodeInfo *CodeInfo=nullptr)
  Return a copy of the specified function and add it to that function's module.
  */
  
  ValueToValueMapTy VMap;
  Function *ClonedFunc = CloneFunction(OrigFunc, VMap);
  ClonedFunc->setName(clonedFuncName);
  errs() << "Created cloned function: " << ClonedFunc->getName() << "\n";
  return clonedFuncName;

}

bool checkFunction(Function &F){
  if (F.isDeclaration()) {
    //errs() << "Skipping function " << F.getName() << " as it is a declaration\n";
    return false;
  }

  if (F.empty()) {
    //errs() << "Skipping function " << F.getName() << " as it is empty\n";
    return false;
  }

  // Skipping functions with names starting with "__"
  if (F.getName().startswith("__")) {
      return false;
  }

  // Skipping main function (Entry point)
  if (F.getName() == "main") {
      return false;
  }

  // Skipping functions with names containing "global" or "init"
  if (F.getName().contains("global") || F.getName().contains("GLOBAL") || F.getName().contains("init")) {
      return false;
  }

  // Skipping functions with the "noreturn" attribute
  if (F.hasFnAttribute(Attribute::NoReturn)) {
      return false;
  }

  // Skipping functions with the "alwaysinline" attribute
  if (F.hasFnAttribute(Attribute::AlwaysInline)) {
      return false;
  }
  return true;
}

bool replaceCall(Module &M, std::string cloneName, std::string origName){
  errs() << "Replacing calls of " << origName << " with " << cloneName << "...\n";
  Function *clonedFunction = M.getFunction(cloneName);
  Function *originalFunction = M.getFunction(origName);

  originalFunction->replaceAllUsesWith(clonedFunction);
  originalFunction->eraseFromParent();

  return true; 
}

bool insertCloneCall(Module &M, std::string cloneName, std::string origName){
  errs() << "Inserting clone call for " << cloneName << "...\n";
  Function *clonedFunction = M.getFunction(cloneName);
  Function *originalFunction = M.getFunction(origName);

  bool retVal = false;


  for (Module::iterator it = M.begin(); it != M.end(); ++it) {
    if (Function* F = dyn_cast<Function>(&*it)) {
      // Skip the cloned function
      if (F == clonedFunction) {
        continue;
      }

      // Iterate over the instructions in the function
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        Instruction* Inst = &*I;

        // Check if the instruction is a function call or invoke
        //invoke is a call with error handeling
        bool found = false;
        Function* calledFunction;
        if (dyn_cast<CallInst>(Inst)){
          found = true;
          CallInst *CI = dyn_cast<CallInst>(Inst);
          calledFunction = CI->getCalledFunction();
          //errs() << "Called Function: " << calledFunction->getName() << "\n";
        }
        else if (dyn_cast<InvokeInst>(Inst)){
          found = true;
          InvokeInst *CI = dyn_cast<InvokeInst>(Inst); 
          calledFunction = CI->getCalledFunction();
          //errs() << "Invoked Function: " << calledFunction->getName() << "\n";
        }
        if (found) {
          // Check if the called function is the one you want to replace
          if (calledFunction == originalFunction) {
            // Create a new IRBuilder
            IRBuilder<> builder(Inst);

            errs() << "Adding call to function clone of " << originalFunction->getName() << "\n";
            std::vector<Value*> args;
            for (auto& arg : originalFunction->args())
            {
              //set up clone function with same arguments as original
              Value* newArg = dyn_cast<Value>(&arg);
              args.push_back(newArg);
            }
            builder.CreateCall(clonedFunction,args);
            retVal = true;
            errs() << "Successfully created call to " << clonedFunction->getName() << "\n";
            

          }
        }
      }
    }
  }
  //return true;
  return retVal;
}

bool insertPrintf(Module &M) {
  bool InsertedAtLeastOnePrintf = false;
  auto &CTX = M.getContext();
  PointerType *PrintfArgTy = PointerType::getUnqual(Type::getInt8Ty(CTX));

  // STEP 1: Inject the declaration of printf
  // ----------------------------------------
  // Create (or _get_ in cases where it's already available) the following
  // declaration in the IR module:
  //    declare i32 @printf(i8*, ...)
  // It corresponds to the following C declaration:
  //    int printf(char *, ...)
  FunctionType *PrintfTy = FunctionType::get(
      IntegerType::getInt32Ty(CTX),
      PrintfArgTy,
      /*IsVarArgs=*/true);

  FunctionCallee Printf = M.getOrInsertFunction("printf", PrintfTy);

  // Set attributes as per inferLibFuncAttributes in BuildLibCalls.cpp
  Function *PrintfF = dyn_cast<Function>(Printf.getCallee());
  PrintfF->setDoesNotThrow();
  PrintfF->addParamAttr(0, Attribute::NoCapture);
  PrintfF->addParamAttr(0, Attribute::ReadOnly);


  // STEP 2: Inject a global variable that will hold the printf format string
  // ------------------------------------------------------------------------
  llvm::Constant *PrintfFormatStr = llvm::ConstantDataArray::getString(
      CTX, "Called Function: %s (Arguments: %d)\n");

  Constant *PrintfFormatStrVar =
      M.getOrInsertGlobal("PrintfFormatStr", PrintfFormatStr->getType());
  dyn_cast<GlobalVariable>(PrintfFormatStrVar)->setInitializer(PrintfFormatStr);

  // STEP 3: For each function in the module, inject a call to printf
  // ----------------------------------------------------------------
  for (auto &F : M) {
    if (!checkFunction(F))
      continue;

    // Get an IR builder. Sets the insertion point to the top of the function
    IRBuilder<> Builder(&*F.getEntryBlock().getFirstInsertionPt());

    // Inject a global variable that contains the function name
    auto FuncName = Builder.CreateGlobalStringPtr(F.getName());

    // Printf requires i8*, but PrintfFormatStrVar is an array: [n x i8]. Add
    // a cast: [n x i8] -> i8*
    llvm::Value *FormatStrPtr =
        Builder.CreatePointerCast(PrintfFormatStrVar, PrintfArgTy, "formatStr");

    // Finally, inject a call to printf
    Builder.CreateCall(
        Printf, {FormatStrPtr, FuncName, Builder.getInt32(F.arg_size())});

    InsertedAtLeastOnePrintf = true;
  }
  return InsertedAtLeastOnePrintf;
}

void dfs(CallGraphNode *Node, std::unordered_set<Function *> &reachableFunctions){
  Function *F = Node->getFunction();
  if (!F || reachableFunctions.count(F) > 0)
    return;

  reachableFunctions.insert(F);

  for (auto &CallRecord : *Node) {
    CallGraphNode *CalleeNode = CallRecord.second;
    dfs(CalleeNode, reachableFunctions);
  }
  return;
}

void printStringMap(std::map<std::string, std::string> stringMap){
  for (const auto& pair : stringMap) {
    errs() << "Key: " << pair.first << ", Value: " << pair.second << "\n";
  }
  return;
}

bool ifEncompassedFunction(Module &M, std::string startFuncName){
  // NOTE: the startF Function is not within the loop, but one of the functions that it
  // calls is
  Function *F = M.getFunction(startFuncName);

  // (1) get all functions reachable from this function
  // TO DO: Lazily get call graph for a specific function instead of the whole module??
  
  // get call graph
  CallGraph CG = CallGraph(M);

  // Perform depth-first search starting from the root node
  // to get Reachable functions
  std::unordered_set<Function *> reachableFunctions;
  CallGraphNode *RootNode = CG[F];
  dfs(RootNode, reachableFunctions);

  // Print the reachable functions
  /*for (Function *ReachableFunc : reachableFunctions) {
    errs() << "Reachable function: " << demangle((ReachableFunc->getName()).str()) << "\n";
  }*/

  // clone all reachable functions
  std::map<std::string, std::string> FuncNameMap;
  for (auto *func : reachableFunctions){
    std::string str = demangle(func->getName().str());
    std::string prefix = "std::";
    if ( str.substr(0, prefix.length()) == prefix ){
      errs() << "Skipping Standard Library Functions for now\n";
      continue;
    }
    std::string cloneName = CloneTheFunction(M, func->getName().str());
    //Function* cf = M.getFunction(cloneName);
    //cf->removeFnAttr(Attribute::NoInline);
    //cf->addFnAttr(Attribute::AlwaysInline);
    FuncNameMap[func->getName().str()] = cloneName;
  }
  //printStringMap(FuncNameMap);

  // replace calls to clones from within cloned functions
  // iterate through map
  // if find call to orig function, use map to replace with clone
  std::vector<Instruction*> toRemove;
  for (const auto& pair : FuncNameMap) {
    const std::string& cloneName = pair.second;
    // Do something with the value
    Function *cloneF = M.getFunction(cloneName);
    if (cloneF) {
      for (Function::iterator BB = cloneF->begin(), BBEnd = cloneF->end(); BB != BBEnd; ++BB) {
        for (BasicBlock::iterator I = BB->begin(), IEnd = BB->end(); I != IEnd; ++I) {
          Instruction* inst = &(*I);
          // Process the instruction
          Function* calledFunction;
          bool found = false;
          //bool invoke = false;
          if (dyn_cast<CallInst>(inst)){
            found = true;
            CallInst *CI = dyn_cast<CallInst>(inst);
            calledFunction = CI->getCalledFunction();
          }
          else if (dyn_cast<InvokeInst>(inst)){
            found = true;
            InvokeInst *CI = dyn_cast<InvokeInst>(inst); 
            calledFunction = CI->getCalledFunction();
          }
          if (found){
            // Create a new IRBuilder
            IRBuilder<> builder(inst);
            auto it = FuncNameMap.find(calledFunction->getName().str());
            if (it != FuncNameMap.end()) {
              //errs() << "Found Replacement Function" << it->second << "\n";
            } else {
              //errs() << "No Function Found in MAP\n";
              continue;
            }

            Function *replacementFunction = M.getFunction(it->second);
            //TO DO: ACcount for invoke
            CallInst *callnst = dyn_cast<CallInst>(inst);
            std::vector<Value*> args;
            errs() << "Inst: " << *callnst << "\n";
            // -1 because the last argument is the function to call
            // which we want to be our new function
            for (unsigned int i = 0; i < callnst->getNumOperands()-1; ++i) {
              Value* originalArg = callnst->getOperand(i);
              errs() << "\tArg: " << *originalArg << "\n";
              args.push_back(originalArg);
            }
            
            /*errs() << "Getting Arguments for " << *replacementFunction << "\n";
            for (auto& arg : calledFunction->args())
            {
              //set up clone function with same arguments as original
              Value* newArg = dyn_cast<Value>(&arg);
              errs() << "Argument: " << arg << "\n";
             // Argument* newArg = new Argument(arg.getType(), arg.getName(), replacementFunction);
              args.push_back(newArg);
            }*/
            CallInst* newCallInst = builder.CreateCall(replacementFunction,args);
            errs() << "New Call Instruction: " << *newCallInst << "\n";
            
            //inst->replaceAllUsesWith(newCallInst);
            toRemove.push_back(callnst);
            //retVal = true;
            errs() << "Successfully created call to " << replacementFunction->getName();
            errs() << " from within " << cloneF->getName() << "\n";
          }
        }
      }
    }
  }

  for (Instruction* inst : toRemove) {
    inst->eraseFromParent();
  } 
  // LATER TODO: determine if any of these functions are in a seperate loop
  // Need to look at what Decker already has to do this

  return true;
}

bool cloneAll(Module &M){
  bool modified = false;
  std::vector<std::string> functionNames;
  std::vector<std::string> clonedFuncNames;

  /**********************  START: Clone all Functions & Replce Calls with Clones **********************/
  // Collect names
  errs() << "--------COLLECTING FUNCTIONS FOR CLONING--------\n";
  for (auto &F : M) {
    if (checkFunction(F)) {
      errs() << "Adding function " << F.getName() << " to clone list for processing\n";
      functionNames.push_back(F.getName().str());
    }
  }
  // Clone
  errs() << "--------CLONING ALL FUNCTIONS--------\n";
  for (const auto &name : functionNames){
    std::string cloneName = CloneTheFunction(M, name);
    clonedFuncNames.push_back(cloneName);
    modified = true; 
  }
  // Repalce original function with clone
  int size = clonedFuncNames.size();
  bool callInserted = false;
  errs() << "--------REPLACING WITH CLONE CALLS--------\n";
  for (int i = 0; i < size; i++){
    callInserted = replaceCall(M, clonedFuncNames[i], functionNames[i]);
    if (!callInserted){
      errs() << "An error occured inserting cloned function call for " << clonedFuncNames[i] << "!\n";
    }
  }
  /**********************  END: Clone all Functions & Replce Calls with Clones **********************/

  
  /******* START: Insert print functions for all cloned & original functions *******/
  errs() << "--------Injecting PRINTF calls--------\n";
  insertPrintf(M);
  /******* END: Insert print functions for all cloned & original functions *******/

  return modified;
}

bool FunctionCloningPass::runOnModule(Module &M) {

  // Anlaysis occurs to deteremine if we have iterated through an encompassed function
  // We simulate this by running through all functions until we find functionZ
  // (we know it calls an encompassed function)

  for (auto &F : M) {
    if (!checkFunction(F))
      continue;
    std::string demangledName = demangle(F.getName().str());
    //errs() << "Demangled Name: " << demangledName << "\n";
    if (demangledName == "functionZ()"){
      //Encompassed Function Found!
      ifEncompassedFunction(M, F.getName().str());
    }
  }

  errs() << "--------Injecting PRINTF calls--------\n";
  insertPrintf(M);

  errs() << "---TEST REPLACEMENT OF CALL TO functionZ()---\n";
  for (auto &F : M) {
    if (!checkFunction(F))
      continue;
    //errs() << "Checking Function: " << F.getName() << "\n";
    for (Function::iterator BB = F.begin(), BBEnd = F.end(); BB != BBEnd; ++BB) {
        for (BasicBlock::iterator I = BB->begin(), IEnd = BB->end(); I != IEnd; ++I) {
          Instruction* inst = &(*I);
          Function* calledFunction;
          bool found = false;
          if (dyn_cast<CallInst>(inst)){
            CallInst *CI = dyn_cast<CallInst>(inst);
            calledFunction = CI->getCalledFunction();
            if (demangle(calledFunction->getName().str()) == "functionZ()"){
              std::string cloneName = calledFunction->getName().str() + '`';
              Value* replacementCallee = M.getFunction(cloneName);
              CI->setCalledOperand(replacementCallee);
            }
            //errs() << "Called Function: " << CI->getCalledFunction()->getName() << "\n";
          }
          else if (dyn_cast<InvokeInst>(inst)){
            InvokeInst *CI = dyn_cast<InvokeInst>(inst); 
            calledFunction = CI->getCalledFunction();
            if (demangle(calledFunction->getName().str()) == "functionZ()"){
              std::string cloneName = calledFunction->getName().str() + '`';
              Value* replacementCallee = M.getFunction(cloneName);
              CI->setCalledOperand(replacementCallee);
            }
            //errs() << "Invoked Function: " << CI->getCalledFunction()->getName() << "\n";
          }
          if (found){
            errs() << "Creating call\n";
            IRBuilder<> builder(inst);
            std::string cloneName = calledFunction->getName().str() + '`';
            Function *funcZclone = M.getFunction(cloneName);
            errs() << "Clone Name: " << cloneName << "\n";
            
            std::vector<Value*> args;
            for (auto& arg : calledFunction->args())
            {
              //set up clone function with same arguments as original
              Value* newArg = dyn_cast<Value>(&arg);
              args.push_back(newArg);
            }

            builder.CreateCall(funcZclone,args);
            errs() << "Repalced FunctionZ call with " << funcZclone->getName() << "\n";

          }
        }
    }
  }

  //bool modified = cloneAll(M);
  errs() << "--------PASS COMPLETED--------\n";

  //return modified;
  return true;
}

PreservedAnalyses FunctionCloningPass::run(Module &M,ModuleAnalysisManager &AM) {
  bool Changed = runOnModule(M);

  return (Changed ? llvm::PreservedAnalyses::none() : llvm::PreservedAnalyses::all());
}
