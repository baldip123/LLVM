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
struct CountDynamicInstructionsPass : public FunctionPass {
  static char ID;
  CountDynamicInstructionsPass() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    Module* M = F.getParent();
    LLVMContext &Context = M->getContext();

    auto updateFunction = M->getOrInsertFunction("updateInstrInfo", Type::getVoidTy(Context), Type::getInt32Ty(Context), Type::getInt32PtrTy(Context), Type::getInt32PtrTy(Context));
    auto printFunction = M->getOrInsertFunction("printOutInstrInfo", Type::getVoidTy(Context));
    
    
    for (Function::iterator blk = F.begin(), e = F.end(); blk != e; ++blk){
        //find the count of each type of instruction in the basic block
        std::map<unsigned, unsigned> InstructionCountMap;
        for (BasicBlock::iterator inst = blk->begin(), e = blk->end(); inst != e; ++inst){
            unsigned opCode = inst->getOpcode();
            InstructionCountMap[opCode] = InstructionCountMap[opCode] + 1;
        }

        
        //instrument the calls at the end at one instruction prior to the end of the basic block,
        //as it must finish with a terminator
        
        //make global arrays out of these both so that you dont have dont load them again each time after the block is executed
        unsigned numInstructionsType =  InstructionCountMap.size();
        auto arraytype = ArrayType::get(Type::getInt32Ty(Context), numInstructionsType);
        
        std::vector<Constant*> keyConstantsVec;
        std::vector<Constant*> valConstantsVec;
        for(auto instCountPair : InstructionCountMap){
          unsigned key = instCountPair.first;
          unsigned val = instCountPair.second;
          keyConstantsVec.push_back(ConstantInt::get(Type::getInt32Ty(Context), key));
          valConstantsVec.push_back(ConstantInt::get(Type::getInt32Ty(Context), val));
        }

        auto keyConstantsArr = ConstantArray::get(arraytype, makeArrayRef(keyConstantsVec));
        auto valConstantsArr = ConstantArray::get(arraytype, makeArrayRef(valConstantsVec));

        auto globalkeysArray = new GlobalVariable(*M, arraytype, true, GlobalVariable::InternalLinkage, keyConstantsArr);
        auto globalvalsArray = new GlobalVariable(*M, arraytype, true, GlobalVariable::InternalLinkage, valConstantsArr);

        Value* idx_list[2] = {ConstantInt::get(Type::getInt64Ty(Context), 0), ConstantInt::get(Type::getInt64Ty(Context), 0)};
        IRBuilder<> builder(blk->getTerminator());
        builder.SetInsertPoint(blk->getTerminator());
        std::vector<Value* > argsVector = {ConstantInt::get(Type::getInt32Ty(Context), numInstructionsType), 
          builder.CreateInBoundsGEP(globalkeysArray, idx_list),
          builder.CreateInBoundsGEP(globalvalsArray, idx_list)
        }; 

        builder.CreateCall(updateFunction, makeArrayRef(argsVector));
        //now add the calls to the update function using the ir builder
    }

    for (Function::iterator blk = F.begin(), e = F.end(); blk != e; ++blk){
      if(std::string(blk->getTerminator()->getOpcodeName()) == "ret"){
        //if the block ends with return only then add the print function
        IRBuilder<> builder(blk->getTerminator());
        builder.SetInsertPoint(blk->getTerminator());
        builder.CreateCall(printFunction);
      }
    }
    
    return false;
  }

  
}; // end of struct TestPass
}  // end of anonymous namespace

char CountDynamicInstructionsPass::ID = 0;
static RegisterPass<CountDynamicInstructionsPass> X("cse231-cdi", "Developed to test LLVM and docker",
                             false /* Only looks at CFG */,
                             true /* Analysis Pass */);