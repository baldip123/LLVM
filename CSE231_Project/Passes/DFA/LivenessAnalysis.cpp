#include"231DFA.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <iostream>
#include <map>
#include <algorithm>

namespace llvm
{
    class LivenessInfo : public Info {
        private : 
            std::set<unsigned> LiveInstructionSet;
        public :
            LivenessInfo(){};
            LivenessInfo(LivenessInfo& Other){
                // I am assuming that this is the copy assignment
                LiveInstructionSet = Other.LiveInstructionSet;
            }
            LivenessInfo(std::set<unsigned> reachingSet){
                LiveInstructionSet = reachingSet;
            }

            void print(){
                for (auto const &e: LiveInstructionSet) {
                    errs() << e << '|';
                }
                errs() << '\n';
            } 

            static bool equals(LivenessInfo * info1, LivenessInfo * info2){
                return info1->LiveInstructionSet == info2->LiveInstructionSet;
            }
            
            /*
            * Joins 2 informatation
            *
            * Direction:
            * 	 Both these information must be distinct from the result
            * 	 The object pointed to by the pointer result must be a proper info object
            */
            static LivenessInfo* join(LivenessInfo * info1, LivenessInfo * info2){
                std::set<unsigned> newset;
                newset.insert(info1->LiveInstructionSet.begin(), info1->LiveInstructionSet.end());
                newset.insert(info2->LiveInstructionSet.begin(), info2->LiveInstructionSet.end());
                LivenessInfo* result = new LivenessInfo(newset);
                return result;
            }
            static void removeFromSet(LivenessInfo * info, std::set<unsigned> removeSet){
                for(unsigned elem:removeSet){
                    info->LiveInstructionSet.erase(elem);
                }
            }
            static void removeFromSet(LivenessInfo * info, unsigned removeElem){
                info->LiveInstructionSet.erase(removeElem);
            }
    };

    

    



class LivenessAnalysis : public DataFlowAnalysis<LivenessInfo, false> {
	
    public:

        LivenessAnalysis(LivenessInfo & bottom, LivenessInfo & initialState) : 
            DataFlowAnalysis<LivenessInfo, false>::DataFlowAnalysis(bottom, initialState) {}

        /*
        * Joins 2 informatation
        *
        * Direction:
        * 	 
        * 	 The object pointed to by the pointer result must be a newly declared Info and must be empty
        */
        LivenessInfo* combineInfoFromIncomingEdges(Instruction* I, std::vector<unsigned> & IncomingEdges){
            unsigned inst_index = InstrToIndex[I];
            auto result = new LivenessInfo();

            for(auto source_node_index:IncomingEdges){
                auto curr_edge = Edge(source_node_index, inst_index);
                LivenessInfo* temp_result = LivenessInfo::join(result, EdgeToInfo[curr_edge]);
                //delete the old result
                delete result;
                result = temp_result;
            }
            return result;
        }
        
        void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges, std::vector<unsigned> & OutgoingEdges, std::vector<LivenessInfo *> & Infos){
            LivenessInfo* inInfo = combineInfoFromIncomingEdges(I, IncomingEdges);
            unsigned inst_index = InstrToIndex[I];
            if(I->isBinaryOp()||I->isBitwiseLogicOp()||std::string(I->getOpcodeName())=="alloca"||
            std::string(I->getOpcodeName())=="load"||
            std::string(I->getOpcodeName())=="getelementptr"||std::string(I->getOpcodeName())=="icmp"||
            std::string(I->getOpcodeName())=="fcmp"||std::string(I->getOpcodeName())=="select"){
                std::set<unsigned> operandsInstructionsSet;
                for(auto op = I->op_begin(), e = I->op_end(); op != e; op++){
                    Instruction* opInst = dyn_cast<Instruction>(&*op);
                    //this will be null if the operand is not the result of an instructions
                    if(opInst){
                        operandsInstructionsSet.insert(InstrToIndex[opInst]);
                    }   
                } 
                LivenessInfo* operandsInfo = new LivenessInfo(operandsInstructionsSet);
                LivenessInfo* outInfo = LivenessInfo::join(inInfo, operandsInfo);
                delete inInfo;
                delete operandsInfo;
                LivenessInfo::removeFromSet(outInfo, inst_index);
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new LivenessInfo(*outInfo));
                }
                delete outInfo;
            }
            else if(std::string(I->getOpcodeName())=="phi"){
                BasicBlock* B = I->getParent();
                std::set<unsigned> phiInstructionsSet;
                for (BasicBlock::iterator i = B->begin(), e = B->end(); i != e; ++i){
                    if(std::string(i->getOpcodeName())=="phi"){
                        phiInstructionsSet.insert(InstrToIndex[&*i]);
                    }
                }
                
                //making a set corresponding to each of the outgoing edges for the phi operands 
                //which will be propogated back to them
                std::map<BasicBlock*, std::set<unsigned>* > blockToPhiOperandMap;

                for(auto& edge:OutgoingEdges){
                    Instruction* inst = IndexToInstr[edge];
                    BasicBlock* block = inst->getParent();
                    //TODO:Delete this
                    blockToPhiOperandMap[block] = new std::set<unsigned>;
                }

                //putting the operands of 
                for (BasicBlock::iterator i = B->begin(), e = B->end(); i != e; ++i){
                    if(std::string(i->getOpcodeName())=="phi"){
                        auto phiInst = dyn_cast<PHINode>(&*i);
                        for(auto op = phiInst->op_begin(), e = phiInst->op_end(); op != e; op++){
                            Instruction* opInst = dyn_cast<Instruction>(&*op);
                            //this will be null if the operand is not the result of an instructions
                            //like when it is a constant
                            if(opInst){
                                auto opIndex = InstrToIndex[opInst];
                                blockToPhiOperandMap[phiInst->getIncomingBlock(*op)]->insert(opIndex);
                            }   
                        } 
                    }
                }

                for(auto& edge:OutgoingEdges){
                    Instruction* inst = IndexToInstr[edge];
                    BasicBlock* block = inst->getParent();
                    LivenessInfo* operandsInfo = new LivenessInfo(*blockToPhiOperandMap[block]);
                    LivenessInfo* outInfo = LivenessInfo::join(inInfo, operandsInfo); 
                    delete inInfo;
                    delete operandsInfo;
                    delete blockToPhiOperandMap[block];
                    LivenessInfo::removeFromSet(outInfo, phiInstructionsSet);
                    //dont delete outinfo
                    Infos.push_back(outInfo);
                }
            }
            else{
                std::set<unsigned> operandsInstructionsSet;
                for(auto op = I->op_begin(), e = I->op_end(); op != e; op++){
                    Instruction* opInst = dyn_cast<Instruction>(&*op);
                    //this will be null if the operand is not the result of an instructions
                    if(opInst){
                        operandsInstructionsSet.insert(InstrToIndex[opInst]);
                    }   
                } 
                LivenessInfo* operandsInfo = new LivenessInfo(operandsInstructionsSet);
                LivenessInfo* outInfo = LivenessInfo::join(inInfo, operandsInfo);
                delete inInfo;
                delete operandsInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new LivenessInfo(*outInfo));
                }
                delete outInfo;
            }
        }

};



namespace {
    struct LivenessAnalysisPass : public FunctionPass {
        static char ID;
        LivenessAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            LivenessInfo bottom;
            LivenessInfo initialState;
            LivenessAnalysis  la(bottom, initialState);

            la.runWorklistAlgorithm(&F);
            la.print();

            return false;
        }
    };
}

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness", "Do reaching definition on CFG",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

} // namespace llvm
