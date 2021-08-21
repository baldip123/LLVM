#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/IRBuilder.h"
// #include "llvm/Support/TypeBuilder.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/GlobalVariable.h"
#include <map>
#include <string>
#include <vector>

using namespace llvm;

namespace {
struct BranchBiasPass : public FunctionPass {
  static char ID;
  BranchBiasPass() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {

    Module* M = F.getParent();
    LLVMContext &Context = M->getContext();

    auto updateFunction = M->getOrInsertFunction("updateBranchInfo", Type::getVoidTy(Context), Type::getInt1Ty(Context));
    auto printFunction = M->getOrInsertFunction("printOutBranchInfo", Type::getVoidTy(Context));
    
    for (Function::iterator blk = F.begin(), e = F.end(); blk != e; ++blk){
      IRBuilder<> builder(blk->getTerminator());
      if(std::string(blk->getTerminator()->getOpcodeName()) == "ret"){
        //if the block ends with return only then add the print function
        builder.SetInsertPoint(blk->getTerminator());
        builder.CreateCall(printFunction);
      }

    //   if(std::string(blk->getTerminator()->getOpcodeName()) == "br"){
    //     //if the block ends with branch only then add the update function with the parameter as the branch condition function
    //     builder.SetInsertPoint(blk->getTerminator());
    //     auto branchCondition = dyn_cast<BranchInst>(blk->getTerminator())->getCondition();
    //     std::vector<Value*> argsVector = {branchCondition};
    //     builder.CreateCall(updateFunction, makeArrayRef(argsVector));
    //   }

      if(std::string(blk->getTerminator()->getOpcodeName()) == "br"){
        //if the block ends with branch only then add the update function with the parameter as the branch condition function
        builder.SetInsertPoint(blk->getTerminator());
        auto branchInst = dyn_cast<BranchInst>(blk->getTerminator());
        if(branchInst->isConditional()){
            auto branchCondition = branchInst->getCondition();
            std::vector<Value*> argsVector = {branchCondition};
            builder.CreateCall(updateFunction, makeArrayRef(argsVector));
        }
      }
    }
    return false;
  }

  
}; // end of struct TestPass
}  // end of anonymous namespace

char BranchBiasPass::ID = 0;
static RegisterPass<BranchBiasPass> X("cse231-bb", "Developed to test LLVM and docker",
                             false /* Only looks at CFG */,
                             true /* Instrumentation Pass */);