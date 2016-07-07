
#include "llvm/Pass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <algorithm>

using namespace llvm;
using namespace std;

namespace {
  struct XLCleanup : public ModulePass {
    static char ID;
    XLCleanup() : ModulePass(ID) {}

    bool runOnModule(Module &M) override {
      bool didSomething = false;
      // Handle any declarations
      for (auto g = M.global_begin(), e = M.global_end(); g != e; ++g) {
        if(g->getName()[0] == '$') {
          string name = g->getName();
          name.erase(remove(name.begin(), name.end(), '$'), name.end());
          errs() << "Global rename: " << g->getName() << " -> " << name << "\n";
          g->setName(name);
          didSomething = true;
        }
      }

      for (auto F = M.begin(), e = M.end(); F != e; ++F) {
        // Handle any instructions
        for (auto bb = F->begin(), e = F->end(); bb != e; ++bb) {
          for (auto i = bb->begin(), e = bb->end(); i != e; ++i) {
            if(i->getName().find('$') != string::npos) {
              string name = i->getName();
              name.erase(remove(name.begin(), name.end(), '$'), name.end());
              i->setName(name);
              didSomething = true;
            }
          }
        }
      }

      return didSomething;
    }
  };
}

char XLCleanup::ID = 0;
static RegisterPass<XLCleanup> X("xlcleanup", "Fix issues caused by WCode to llvm conversion", false, false);
