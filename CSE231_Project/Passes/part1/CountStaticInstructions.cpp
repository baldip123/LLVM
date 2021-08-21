#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include <map>
#include <string>

using namespace llvm;

namespace {
struct CountStaticInstructionsPass : public FunctionPass {
  static char ID;
  CountStaticInstructionsPass() : FunctionPass(ID) {}

  std::map<std::string, int> InstructionCountMap;
  bool runOnFunction(Function &F) override {

    
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
      Instruction* inst = I.operator->();
      std::string opCode(inst->getOpcodeName());
      InstructionCountMap[opCode] = InstructionCountMap[opCode] + 1;
    }

    errs().write_escaped(F.getName()) << '\n';
    for(auto instCountPair : InstructionCountMap){
        errs().write_escaped(instCountPair.first) << ' ';
        errs().write_escaped(StringRef(std::to_string(instCountPair.second))) << '\n';
    }
    
    return false;
  }

  
}; // end of struct TestPass
}  // end of anonymous namespace

char CountStaticInstructionsPass::ID = 0;
static RegisterPass<CountStaticInstructionsPass> X("cse231-csi", "Developed to test LLVM and docker",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);