
#include "llvm/Pass.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"

#include "llvm/Support/raw_ostream.h"

#include <unordered_map>
#include <unordered_set>

using namespace llvm;

namespace {
  using namespace std;

  typedef unordered_map<BasicBlock *, unordered_set<Instruction *>> LiveMap;

  struct LiveRange : public FunctionPass {
    static char ID;
    LiveRange() : FunctionPass(ID) {}

    LiveMap LiveIn;
    LiveMap LiveOut;

    bool runOnInstructionDFS(Instruction *i, BasicBlock *bb, unordered_set<Instruction *>& users, unordered_set<BasicBlock *>& visited) {
      if(visited.count(bb) > 0) // Already visited
        return LiveIn[bb].count(i) > 0; // Visited block contained a use or through-use of i
      visited.insert(bb);

      bool found = false;
      for (auto I = bb->begin(), e = bb->end(); I != e; ++I) {
        found |= users.count(&*I) > 0; // Found a use in this basic block
      }

      bool foundBelow = false;
      for (auto S = succ_begin(bb), e = succ_end(bb); S != e; ++S) {
        foundBelow |= runOnInstructionDFS(i, *S, users, visited);
      }

      if (found || foundBelow) {
        LiveIn[bb].insert(i);
      } if (foundBelow) {
        LiveOut[bb].insert(i);
      }

      return found || foundBelow;
    }

    void runOnInstruction(Instruction *i) {
      BasicBlock *BB = i->getParent();

      // Build the inter-block users set
      unordered_set<Instruction *> users;
      for (auto u = i->use_begin(), e = i->use_end(); u != e; ++u) {
        if (Instruction *user = dyn_cast<Instruction>(u->getUser())) {
          if (user->getParent() != BB) {
            users.insert(user);
          }
        } else {
          assert(false && "User found that is not an instruction");
        }
      }

      if (users.empty()) {
        return;
      }

      unordered_set<BasicBlock *> visited;
      visited.insert(BB);
      LiveOut[BB].insert(i);

      for (auto S = succ_begin(BB), e = succ_end(BB); S != e; ++S) {
        runOnInstructionDFS(i, *S, users, visited);
      }
    }

    void getAnalysisUsage(AnalysisUsage& AU) const override {
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
    }

    bool runOnFunction(Function &F) override {
      // Set up the sets
      for (auto BB = F.begin(), e = F.end(); BB != e; ++BB) {
        LiveIn[&*BB] = unordered_set<Instruction *>();
        LiveOut[&*BB] = unordered_set<Instruction *>();
      }

      // Get live ranges for all instructions
      for (auto BB = F.begin(), e = F.end(); BB != e; ++BB) {
        for (auto I = BB->begin(), e = BB->end(); I != e; ++I) {
          runOnInstruction(&*I);
        }
      }

      // Print out the results
      for (auto BB = F.begin(), e = F.end(); BB != e; ++BB) {
        errs() << "\n\nBasic Block: " << BB->getName() << "\n";
        for (auto in = LiveIn[&*BB].begin(), e = LiveIn[&*BB].end(); in != e; ++in) {
          if(LiveOut[&*BB].count(*in) == 0) // Only in
            errs() << " IN   " << (*in)->getName() << " from " << (*in)->getParent()->getName() << "\n";
        }
        for (auto out = LiveOut[&*BB].begin(), e = LiveOut[&*BB].end(); out != e; ++out) {
          if(LiveIn[&*BB].count(*out) == 0) // Only out
            errs() << " OUT  " << (*out)->getName() << "\n";
        }
        for (auto in = LiveIn[&*BB].begin(), e = LiveIn[&*BB].end(); in != e; ++in) {
          if(LiveOut[&*BB].count(*in) != 0) // Live across
            errs() << " THRU " << (*in)->getName() << " from " << (*in)->getParent()->getName() << "\n";
        }
      }
      return false;
    }
  };
}
char LiveRange::ID = 0;
static RegisterPass<LiveRange> X("plive", "Print Live-in, Live-out, and Live-across variables", false, false);
