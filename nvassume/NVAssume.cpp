#include "llvm/Pass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/InstrTypes.h"

#include <string>
#include <unordered_map>

#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "nvassume"

namespace {

  struct Range {
    Range() {}
    Range(long min, long max) : min(min), max(max) {}
    long min;
    long max;
  };


  struct NVAssume : public FunctionPass {
    static char ID;
    NVAssume() : FunctionPass(ID) {}

    std::unordered_map<std::string, Range> intrinsics = {
      {"llvm.nvvm.read.ptx.sreg.tid.x", Range(0, 1023)},
      {"llvm.nvvm.read.ptx.sreg.tid.y", Range(0, 1023)},
      {"llvm.nvvm.read.ptx.sreg.tid.z", Range(0, 63)},
      {"llvm.nvvm.read.ptx.sreg.ntid.x", Range(1, 1023)},
      {"llvm.nvvm.read.ptx.sreg.ntid.y", Range(1, 1023)},
      {"llvm.nvvm.read.ptx.sreg.ntid.z", Range(1, 63)},
      {"llvm.nvvm.read.ptx.sreg.ctaid.x", Range(0, 2147483645)},
      {"llvm.nvvm.read.ptx.sreg.ctaid.y", Range(0, 65534)},
      {"llvm.nvvm.read.ptx.sreg.ctaid.z", Range(0, 65534)},
      {"llvm.nvvm.read.ptx.sreg.nctaid.x", Range(1, 2147483646)},
      {"llvm.nvvm.read.ptx.sreg.nctaid.y", Range(1, 65535)},
      {"llvm.nvvm.read.ptx.sreg.nctaid.z", Range(1, 65535)},
      {"llvm.nvvm.read.ptx.sreg.warpsize", Range(16, 64)}
    };

    void getAnalysisUsage(AnalysisUsage& AU) const override {
    }


    bool runOnFunction(Function &F) override {
      LLVMContext& Ctx = F.getContext();

      bool injected = false;
      Function *assume = Intrinsic::getDeclaration(F.getParent(), Intrinsic::assume);
      DEBUG(dbgs() << "Assume name: " << assume->getName() << "\n");

      for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
        for (auto i = bb->begin(), e = bb->end(); i != e; ++i) {

          if(CallInst *c = dyn_cast<CallInst>(i)) {
            if(intrinsics.count(c->getCalledFunction()->getName()) > 0) {
              DEBUG(dbgs() << "Injecting range for " << c->getCalledFunction()->getName() << "\n");
              injected = true;
              Range range = intrinsics[c->getCalledFunction()->getName()];

              ConstantInt *min = ConstantInt::get(Type::getInt32Ty(Ctx), range.min, true);
              ConstantInt *max = ConstantInt::get(Type::getInt32Ty(Ctx), range.max, true);


              ICmpInst *minCmp = new ICmpInst(ICmpInst::Predicate::ICMP_SGE, c, min, "assume_tmp");
              i = bb->getInstList().insert(++i, minCmp);
              ICmpInst *maxCmp = new ICmpInst(ICmpInst::Predicate::ICMP_SLE, c, max, "assume_tmp");
              i = bb->getInstList().insert(++i, maxCmp);

              ArrayRef<Value *> minArgs(minCmp);
              CallInst *minCall = CallInst::Create(assume, minArgs, "");
              i = bb->getInstList().insert(++i, minCall);

              ArrayRef<Value *> maxArgs(maxCmp);
              CallInst *maxCall = CallInst::Create(assume, maxArgs, "");
              i = bb->getInstList().insert(++i, maxCall);
            }
          }
        }
      }
      return injected;
    }
  };
}

char NVAssume::ID = 0;
static RegisterPass<NVAssume> X("nvassume", "Inject NVidia Intrinsic Assumptions", false, false);
