#include "llvm/Pass.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/Loads.h"
#include "llvm/Analysis/PostDominators.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"

#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <vector>
#include <unordered_map>
#include <unordered_set>


using namespace llvm;

namespace {
  class Chain {
  private:
    std::vector<BasicBlock *> chain;
    std::unordered_map<BasicBlock *, std::vector<BasicBlock *>> between;
  public:
    Chain(BasicBlock * root) {
      chain.push_back(root);
    }

    bool contains(BasicBlock *BB) {
      for(auto bb = chain.begin(), e = chain.end(); bb != e; ++bb)
        if(*bb == BB)
          return true;
      return false;
    }

    void append(BasicBlock * next) {
      assert(chain.size() > 0);
      BasicBlock * last = chain.back();
      // Insert the new end of the chain
      chain.push_back(next);

      std::unordered_set<BasicBlock *> fromLast;
      std::unordered_set<BasicBlock *> toNext;

      // Initialize the queue
      std::vector<BasicBlock *> queue;
      queue.push_back(last);

      // Find all successors
      while(queue.size() != 0) {
        BasicBlock * BB = queue.back();
        queue.pop_back();
        for(auto s = succ_begin(BB), e = succ_end(BB); s != e; ++s) {
          if(fromLast.count(*s) == 0 && *s != next) {
            fromLast.insert(*s);
            queue.push_back(*s);
          }
        }
      }

      // Initialize the queue
      queue.push_back(next);

      // Find all predecessors
      while(queue.size() != 0) {
        BasicBlock * BB = queue.back();
        queue.pop_back();
        for(auto p = pred_begin(BB), e = pred_end(BB); p != e; ++p) {
          if(toNext.count(*p) == 0 && *p != last) {
            toNext.insert(*p);
            queue.push_back(*p);
          }
        }
      }

      // Calculate the overlapping intersection
      std::vector<BasicBlock *> intersection;
      for(auto bb = fromLast.begin(), e = fromLast.end(); bb != e; ++bb)
        if(toNext.count(*bb) > 0)
          intersection.push_back(*bb);

      // Assign the possible nodes between the basic blocks
      between[last] = intersection;
    }


    void dump() {
      errs() << "Chain (" << chain.size() << " blocks)\n";
      for(auto bb = chain.begin(), e = chain.end(); bb != e; ++bb) {
        errs() <<"- " << (*bb)->getName() << "\n";
      }
    }

    size_t size() {
      return chain.size();
    }

    BasicBlock *operator[](size_t i) {
      return chain[i];
    }

    const std::vector<BasicBlock *>& blocksBetween(size_t i) {
      return between[chain[i]];
    }

    static bool singleElem(Chain& chain) {
      return chain.chain.size() == 1;
    }
  };
  struct MinReg : public FunctionPass {
    static char ID;
    MinReg() : FunctionPass(ID) {}
    AliasAnalysis *AA;
    DominatorTree *DT;
    PostDominatorTree *PDT;

    void getAnalysisUsage(AnalysisUsage& AU) const override {
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<PostDominatorTreeWrapperPass>();
      AU.addRequired<AAResultsWrapperPass>();
    }

    void createChains(std::vector<Chain>& chains, BasicBlock * BB) {
      errs() << "Starting chain with " << BB->getName() << "\n";
      chains.push_back(Chain(BB));
      size_t index = chains.size()-1;
      bool didSomething = true;

      while(didSomething) {
        didSomething = false;
        for(auto s = succ_begin(BB), e = succ_end(BB); s != e; ++s) {
          if(DT->dominates(BB, *s) && PDT->dominates(*s, BB)) {

            errs() << "Appending " << (*s)->getName() << " to chain\n";
            // Attach to the current chain
            chains[index].append(*s);
            BB = *s;
            didSomething = true;
          } else {
            bool contained = false;
            for(auto c = chains.begin(), e = chains.end(); c != e; ++c) {
              contained = contained || c->contains(*s);
            }
            if(!contained) {
              // Begin a new chain
              createChains(chains, *s);
            }
          }
        }
      }
    }

    bool canMoveInst(Instruction &I, AliasSetTracker &AST) {
      if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
        if (!LI->isUnordered())
          return false; // Don't hoist volatile/atomic loads!

        // Loads from constant memory are always safe to move, even if they end up
        // in the same alias set as something that ends up being modified.
        if (AA->pointsToConstantMemory(LI->getOperand(0)))
          return true;
        if (LI->getMetadata(LLVMContext::MD_invariant_load))
          return true;

        // Don't move loads that may have been written to between
        uint64_t Size = 0;
        if (LI->getType()->isSized())
          Size = I.getModule()->getDataLayout().getTypeStoreSize(LI->getType());

        AAMDNodes AAInfo;
        LI->getAAMetadata(AAInfo);

        return !AST.getAliasSetForPointer(&I, Size, AAInfo).isMod();
      }
      // TODO: Handle call instructions

      if (!isa<BinaryOperator>(I) && !isa<CastInst>(I) && !isa<SelectInst>(I) &&
          !isa<GetElementPtrInst>(I) && !isa<CmpInst>(I) &&
          !isa<InsertElementInst>(I) && !isa<ExtractElementInst>(I) &&
          !isa<ShuffleVectorInst>(I) && !isa<ExtractValueInst>(I) &&
          !isa<InsertValueInst>(I))
        return false;

      return true;
    }

    void getMovableUses(std::vector<User*>& uses, BasicBlock *fromBB, BasicBlock *toBB, AliasSetTracker& AST) {
      assert(DT != nullptr);
      bool didSomething = true;
      while (didSomething) {
        didSomething = false;
        for(auto i = fromBB->begin(), e = fromBB->end(); i != e; ++i) {
          // Ensure this instruction can be moved
          if(!canMoveInst(*i, AST)) {
            errs() << "Instruction cannot be moved:\n";
            i->dump();
            continue;
          }

          // Ensure that operands would be accessible/can be moved
          bool opsValid = true;
          for(auto op = i->op_begin(), e = i->op_end(); op != e; ++op) {
            if(std::find(uses.begin(), uses.end(), op->get()) != uses.end())
              continue; // Operand can be moved
            if(Instruction * I = dyn_cast<Instruction>(op->get())) {
              //
              if(I->getParent() == toBB || DT->dominates(I, toBB))
                continue; // Definition covers the target
            } else {
              continue; // Operand isn't an instruction, always safe
            }
            opsValid = false;
          }
          if (!opsValid)
            continue;

          if (std::find(uses.begin(), uses.end(), &*i) == uses.end()) {
            uses.push_back(&*i);
            errs() << "Found Movement Candidate:\n";
            i->dump();
            didSomething = true;
          }
        }
      }
    }

    void raiseUses(Chain& chain) {
      assert(AA != nullptr);
      for(size_t i = chain.size()-1; i > 0; i--) {

        // Generate the AliasSet between these nodes in the chain
        AliasSetTracker *AST = new AliasSetTracker(*AA);
        const std::vector<BasicBlock *>& between = chain.blocksBetween(i-1);
        for(auto bb = between.begin(), e = between.end(); bb != e; ++bb)
          AST->add(**bb);

        // Generate the set of movable uses
        std::vector<User *> uses;
        getMovableUses(uses, chain[i], chain[i-1], *AST);

        errs() << "Candidates from " << chain[i]->getName()
          << " to " << chain[i-1]->getName() << ":\n";
        errs() << "(Through ";
        for(auto b = chain.blocksBetween(i-1).begin(), e = chain.blocksBetween(i-1).end(); b != e; ++b)
          errs() << (*b)->getName() << " ";
        errs() << ")\n";
        for(auto u = uses.begin(), e = uses.end(); u != e; ++u)
          (*u)->dump();
      }
    }

    bool runOnFunction(Function &F) override {
      AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
      DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      PDT = &getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();

      F.viewCFG();
      std::vector<Chain> chains;
      createChains(chains, &F.getEntryBlock());

      // Discard trivial chains
      auto endChains = std::remove_if(chains.begin(), chains.end(), Chain::singleElem);
      // Raise Uses
      for(auto c = chains.begin(); c != endChains; ++c)
        raiseUses(*c);

      return false;
    }
  };
}

char MinReg::ID = 0;
static RegisterPass<MinReg> X("minreg", "Minimize Regiser Usage with Global Code Motion", false, false);
