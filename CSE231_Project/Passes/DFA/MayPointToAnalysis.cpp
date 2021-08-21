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
    class MayPointToInfo : public Info {
        
        public :
            typedef std::pair<char, unsigned> DFAIdentifier ;
            typedef std::pair<DFAIdentifier, DFAIdentifier> PointsToPair; 
            MayPointToInfo(){};
            MayPointToInfo(MayPointToInfo& Other){
                // I am assuming that this is the copy assignment
                PointsToPairsSet = Other.PointsToPairsSet;
            }
            MayPointToInfo(std::set<PointsToPair> pairsSet){
                PointsToPairsSet = pairsSet;
            }

            std::set<DFAIdentifier> getSetOfPointers(){
                std::set<DFAIdentifier> setOfPointers;
                for(auto const & pair:PointsToPairsSet){
                    setOfPointers.insert(pair.first);
                }
                return setOfPointers;
            }

            std::map<DFAIdentifier, std::set<DFAIdentifier>> getMapFromPointerToItsSetOfPointees(){
                auto setOfPointers = getSetOfPointers();
                std::map<DFAIdentifier, std::set<DFAIdentifier>> MapFromPointerToItsSetOfPointees;
                for(auto const& pointer:setOfPointers){
                    MapFromPointerToItsSetOfPointees[pointer] = std::set<DFAIdentifier>();
                }
                for(auto const & pair:PointsToPairsSet){
                    MapFromPointerToItsSetOfPointees[pair.first].insert(pair.second);
                }
                return MapFromPointerToItsSetOfPointees;
            }

            std::set<DFAIdentifier> getSetOfPointees(DFAIdentifier pointer){
                std::set<DFAIdentifier> setOfPointees;
                for(auto const & pair:PointsToPairsSet){
                    if(pair.first == pointer){
                        setOfPointees.insert(pair.second);
                    }
                }
                return setOfPointees;
            }

            void print(){
                auto MapFromPointerToItsSetOfPointees = getMapFromPointerToItsSetOfPointees();
                for (auto const &elem: MapFromPointerToItsSetOfPointees) {
                    auto pointer = elem.first;
                    auto &pointees = elem.second;
                    errs() << pointer.first << pointer.second << "->(";
                    for(auto const &pointee:pointees){
                        errs() << pointee.first << pointee.second << "\\";
                    }
                    errs() << ")|";
                }
                errs() << ")\n";
            } 

            static bool equals(MayPointToInfo * info1, MayPointToInfo * info2){
                return info1->PointsToPairsSet == info2->PointsToPairsSet;
            }
            
            /*
            * Joins 2 informatation
            *
            * Direction:
            * 	 Both these information must be distinct from the result
            * 	 The object pointed to by the pointer result must be a proper info object
            */
            static MayPointToInfo* join(MayPointToInfo * info1, MayPointToInfo * info2){
                std::set<PointsToPair> newset;
                newset.insert(info1->PointsToPairsSet.begin(), info1->PointsToPairsSet.end());
                newset.insert(info2->PointsToPairsSet.begin(), info2->PointsToPairsSet.end());
                MayPointToInfo* result = new MayPointToInfo(newset);
                return result;
            }

        private : 
            std::set<PointsToPair> PointsToPairsSet;
    };

    

    



class MayPointToAnalysis : public DataFlowAnalysis<MayPointToInfo, true> {
	
    public:

        MayPointToAnalysis(MayPointToInfo & bottom, MayPointToInfo & initialState) : 
            DataFlowAnalysis<MayPointToInfo, true>::DataFlowAnalysis(bottom, initialState) {}

        /*
        * Joins 2 informatation
        *
        * Direction:
        * 	 
        * 	 The object pointed to by the pointer result must be a newly declared Info and must be empty
        */
        MayPointToInfo* combineInfoFromIncomingEdges(Instruction* I, std::vector<unsigned> & IncomingEdges){
            unsigned inst_index = InstrToIndex[I];
            auto result = new MayPointToInfo();
            for(auto source_node_index:IncomingEdges){
                auto curr_edge = Edge(source_node_index, inst_index);
                MayPointToInfo* temp_result = MayPointToInfo::join(result, EdgeToInfo[curr_edge]);
                //delete the old result
                delete result;
                result = temp_result;
            }
            return result;
        }
        
        void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges, std::vector<unsigned> & OutgoingEdges, std::vector<MayPointToInfo *> & Infos){
            MayPointToInfo* inInfo = combineInfoFromIncomingEdges(I, IncomingEdges);
            unsigned inst_index = InstrToIndex[I];

            if(std::string(I->getOpcodeName())=="alloca"){
                unsigned instIndex = InstrToIndex[I];
                auto pointer = MayPointToInfo::DFAIdentifier('R', inst_index);
                auto pointee = MayPointToInfo::DFAIdentifier('M', inst_index);
                auto pointerPointeePair = MayPointToInfo::PointsToPair(pointer, pointee);
                std::set<MayPointToInfo::PointsToPair> currInstSet = {pointerPointeePair};
                MayPointToInfo* currInstInfo = new MayPointToInfo(currInstSet);
                MayPointToInfo* outInfo = MayPointToInfo::join(inInfo, currInstInfo);
                delete currInstInfo;
                delete inInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new MayPointToInfo(*outInfo));
                }
                delete outInfo;
            }
            else if(std::string(I->getOpcodeName())=="bitcast"){
                unsigned instIndex = InstrToIndex[I];
                auto bitCastInst = dyn_cast<BitCastInst>(I);
                auto operandInst = dyn_cast<Instruction>(bitCastInst->getOperand(0));
                auto operandInstIndex = InstrToIndex[operandInst];

                auto operandPointer = MayPointToInfo::DFAIdentifier('R', operandInstIndex);
                auto resultPointer = MayPointToInfo::DFAIdentifier('R', inst_index);

                std::set<MayPointToInfo::PointsToPair> currInstSet;
                auto setOfPointees = inInfo->getSetOfPointees(operandPointer);

                for(auto pointee : setOfPointees){
                    currInstSet.insert(MayPointToInfo::PointsToPair(resultPointer, pointee));
                }

                MayPointToInfo* currInstInfo = new MayPointToInfo(currInstSet);
                MayPointToInfo* outInfo = MayPointToInfo::join(inInfo, currInstInfo);
                delete currInstInfo;
                delete inInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new MayPointToInfo(*outInfo));
                }
                delete outInfo;
            }
            else if(std::string(I->getOpcodeName())=="getelementptr"){
                unsigned instIndex = InstrToIndex[I];
                auto gepInst = dyn_cast<GetElementPtrInst>(I);
                auto operandInst = dyn_cast<Instruction>(gepInst->getPointerOperand());
                auto operandInstIndex = InstrToIndex[operandInst];

                auto operandPointer = MayPointToInfo::DFAIdentifier('R', operandInstIndex);
                auto resultPointer = MayPointToInfo::DFAIdentifier('R', inst_index);

                std::set<MayPointToInfo::PointsToPair> currInstSet;
                auto setOfPointees = inInfo->getSetOfPointees(operandPointer);

                for(auto pointee : setOfPointees){
                    currInstSet.insert(MayPointToInfo::PointsToPair(resultPointer, pointee));
                }

                MayPointToInfo* currInstInfo = new MayPointToInfo(currInstSet);
                MayPointToInfo* outInfo = MayPointToInfo::join(inInfo, currInstInfo);
                delete currInstInfo;
                delete inInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new MayPointToInfo(*outInfo));
                }
                delete outInfo;
            }
            else if(std::string(I->getOpcodeName())=="load"){
                unsigned instIndex = InstrToIndex[I];
                auto loadInst = dyn_cast<LoadInst>(I);
                auto operandInst = dyn_cast<Instruction>(loadInst->getPointerOperand());
                auto operandInstIndex = InstrToIndex[operandInst];

                auto operandPointer = MayPointToInfo::DFAIdentifier('R', operandInstIndex);
                auto resultPointer = MayPointToInfo::DFAIdentifier('R', inst_index);

                std::set<MayPointToInfo::PointsToPair> currInstSet;
                auto setOfPointees = inInfo->getSetOfPointees(operandPointer);

                for(auto pointee : setOfPointees){
                    auto secondLevelPointeeSet = inInfo->getSetOfPointees(pointee);
                    for(auto secondLevelPointee:secondLevelPointeeSet){
                        currInstSet.insert(MayPointToInfo::PointsToPair(resultPointer, secondLevelPointee));
                    }
                }

                MayPointToInfo* currInstInfo = new MayPointToInfo(currInstSet);
                MayPointToInfo* outInfo = MayPointToInfo::join(inInfo, currInstInfo);
                delete currInstInfo;
                delete inInfo;
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new MayPointToInfo(*outInfo));
                }
                delete outInfo;
            }
            else if(std::string(I->getOpcodeName())=="store"){
                unsigned instIndex = InstrToIndex[I];
                auto storeInst = dyn_cast<StoreInst>(I);
                auto operandPointerInst = dyn_cast<Instruction>(storeInst->getPointerOperand());
                auto operandValueInst = dyn_cast<Instruction>(storeInst->getValueOperand());
                if(operandValueInst){
                    //if this is false that would mean that the value for the store was a constant or something but not an instruction,
                    //in which case the in is just the out

                    auto operandPointer = MayPointToInfo::DFAIdentifier('R', InstrToIndex[operandPointerInst]);
                    auto valuePointer = MayPointToInfo::DFAIdentifier('R',  InstrToIndex[operandValueInst]);

                    std::set<MayPointToInfo::PointsToPair> currInstSet;
                    auto setOfOperandPointees = inInfo->getSetOfPointees(operandPointer);
                    auto setOfValuePointees = inInfo->getSetOfPointees(valuePointer);

                    for(auto operandPointee : setOfOperandPointees){
                        for(auto valuePointee : setOfValuePointees){
                            currInstSet.insert(MayPointToInfo::PointsToPair(operandPointee, valuePointee));
                        }
                    }

                    MayPointToInfo* currInstInfo = new MayPointToInfo(currInstSet);
                    MayPointToInfo* outInfo = MayPointToInfo::join(inInfo, currInstInfo);
                    delete currInstInfo;
                    delete inInfo;
                    for(auto& edge:OutgoingEdges){
                        Infos.push_back(new MayPointToInfo(*outInfo));
                    }
                    delete outInfo;
                }
                else
                {
                    for(auto& edge:OutgoingEdges){
                        Infos.push_back(new MayPointToInfo(*inInfo));
                    }
                    delete inInfo;
                }
                
            }
            //add phi and select instructions cases here
            else{
                for(auto& edge:OutgoingEdges){
                    Infos.push_back(new MayPointToInfo(*inInfo));
                }
                delete inInfo;
            }
        }

};



namespace {
    struct MayPointToAnalysisPass : public FunctionPass {
        static char ID;
        MayPointToAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            MayPointToInfo bottom;
            MayPointToInfo initialState;
            MayPointToAnalysis mpt(bottom, initialState);

            mpt.runWorklistAlgorithm(&F);
            mpt.print();

            return false;
        }
    };
}

char MayPointToAnalysisPass::ID = 0;
static RegisterPass<MayPointToAnalysisPass> X("cse231-maypointto", "Do reaching definition on CFG",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

} // namespace llvm