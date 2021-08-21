#include"231DFA.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <iostream>
#include <algorithm>

namespace llvm
{
    class ReachingInfo : public Info {
        private : 
            std::set<unsigned> reachingInstructionSet;
        public :
            ReachingInfo(){};
            ReachingInfo(ReachingInfo& Other){
                // I am assuming that this is the copy assignment
                reachingInstructionSet = Other.reachingInstructionSet;
            }
            ReachingInfo(std::set<unsigned> reachingSet){
                reachingInstructionSet = reachingSet;
            }

            void print(){
                for (auto const &e: reachingInstructionSet) {
                    errs() << e << '|';
                }
                errs() << '\n';
            } 

            static bool equals(ReachingInfo * info1, ReachingInfo * info2){
                return info1->reachingInstructionSet == info2->reachingInstructionSet;
            }
            
            /*
            * Joins 2 informatation
            *
            * Direction:
            * 	 Both these information must be distinct from the result
            * 	 The object pointed to by the pointer result must be a proper info object
            */
            static ReachingInfo* join(ReachingInfo * info1, ReachingInfo * info2){
                std::set<unsigned> newset;
                newset.insert(info1->reachingInstructionSet.begin(), info1->reachingInstructionSet.end());
                newset.insert(info2->reachingInstructionSet.begin(), info2->reachingInstructionSet.end());
                ReachingInfo* result = new ReachingInfo(newset);
                return result;
            }
    };

    

    



class ReachingDefinitionAnalysis : public DataFlowAnalysis<ReachingInfo, true> {
	
    public:

        ReachingDefinitionAnalysis(ReachingInfo & bottom, ReachingInfo & initialState) : 
            DataFlowAnalysis<ReachingInfo, true>::DataFlowAnalysis(bottom, initialState) {}

        /*
        * Joins 2 informatation
        *
        * Direction:
        * 	 
        * 	 The object pointed to by the pointer result must be a newly declared Info and must be empty
        */
        ReachingInfo* combineInfoFromIncomingEdges(Instruction* I, std::vector<unsigned> & IncomingEdges){
            unsigned inst_index = InstrToIndex[I];
            auto result = new ReachingInfo();
            for(auto source_node_index:IncomingEdges){
                auto curr_edge = Edge(source_node_index, inst_index);
                ReachingInfo* temp_result = ReachingInfo::join(result, EdgeToInfo[curr_edge]);
                //delete the old result
                delete result;
                result = temp_result;
            }
            return result;
        }
        
        void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges, std::vector<unsigned> & OutgoingEdges, std::vector<ReachingInfo *> & Infos){
            ReachingInfo* inInfo = combineInfoFromIncomingEdges(I, IncomingEdges);
            unsigned inst_index = InstrToIndex[I];

            if(I->isBinaryOp()||I->isBitwiseLogicOp()||std::string(I->getOpcodeName())=="alloca"||
            std::string(I->getOpcodeName())=="load"||
            std::string(I->getOpcodeName())=="getelementptr"||std::string(I->getOpcodeName())=="icmp"||
            std::string(I->getOpcodeName())=="fcmp"||std::string(I->getOpcodeName())=="select"){
                std::set<unsigned> curr_inst_set = {inst_index};
                ReachingInfo* currInstInfo = new ReachingInfo(curr_inst_set);
                ReachingInfo* outInfo = ReachingInfo::join(inInfo, currInstInfo);
                delete inInfo;
                delete currInstInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new ReachingInfo(*outInfo));
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
                ReachingInfo* phiInstInfo = new ReachingInfo(phiInstructionsSet);
                ReachingInfo* outInfo = ReachingInfo::join(inInfo, phiInstInfo);
                delete inInfo;
                delete phiInstInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new ReachingInfo(*outInfo));
                }
                delete outInfo;
            }
            else{
                ReachingInfo* outInfo = inInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new ReachingInfo(*outInfo));
                }
                delete outInfo;
            }
        }

};



namespace {
    struct ReachingDefinitionAnalysisPass : public FunctionPass {
        static char ID;
        ReachingDefinitionAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            ReachingInfo bottom;
            ReachingInfo initialState;
            ReachingDefinitionAnalysis  rda(bottom, initialState);

            rda.runWorklistAlgorithm(&F);
            rda.print();

            return false;
        }
    };
}

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching", "Do reaching definition on CFG",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

} // namespace llvm
