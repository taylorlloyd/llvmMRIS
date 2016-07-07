#include "llvm/Pass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"

#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "reduce-width"

namespace {
  struct ReduceWidth : public FunctionPass {
    static char ID;
    ReduceWidth() : FunctionPass(ID) {}

    LazyValueInfo *LVI;

    void getAnalysisUsage(AnalysisUsage& AU) const override {
      AU.addRequired<LazyValueInfoWrapperPass>();
    }

    // Returns a value equal to original, with the target type
    Value *convertSize(Value *original, Type *target) {
      assert(original->getType()->isIntegerTy());
      if(original->getType()->getIntegerBitWidth() == target->getIntegerBitWidth())
        return original;

      if (CastInst *cast = dyn_cast<CastInst>(original)) {
        Value *orig = cast->getOperand(0);
        if (orig->getType() == target) {
          // Stop using the cast entirely
          return orig;
        }
        if (orig->getType()->isIntegerTy()) {
          // Use this as the source value instead
          original = orig;
        }
      }

      if (ConstantInt *ci = dyn_cast<ConstantInt>(original)) {
        //TODO: assert if invalid
        return ConstantInt::get(target, ci->getSExtValue(), true);
      }

      if (Instruction *i = dyn_cast<Instruction>(original)) {
        CastInst *cast;
        if(i->getType()->getIntegerBitWidth() > target->getIntegerBitWidth())
          cast = CastInst::CreateTruncOrBitCast(i, target);
        else
          cast = CastInst::CreateSExtOrBitCast(i, target);

        if (isa<PHINode>(i)) {
          // must not insert a non-PHI instruction before a PHI
          cast->insertBefore(i->getParent()->getFirstNonPHI());
        } else {
          cast->insertAfter(i);
        }
        return cast;
      }
      llvm_unreachable("Tried to convert unknown value's type");
    }

    bool canConvertOperands(unsigned Width, Instruction* i) {
      for (auto op = i->op_begin(), e = i->op_end(); op != e; ++op)
        if (!canConvertToInt(Width, op->get(), i))
          return false;
      return true;
    }

    bool canConvertToInt(unsigned Width, Value *v, Instruction *context) {
      assert(LVI != nullptr);
      assert(v != nullptr);

      if(ICmpInst *cmp = dyn_cast<ICmpInst>(v))
        // Compares don't generate ints, but can still be
        // downsized to use smaller inputs where possible
        return canConvertOperands(Width, cmp);

      if(!v->getType()->isIntegerTy())
        // Integers only
        return false;
      if(v->getType()->getIntegerBitWidth() <= Width)
        // Already sufficiently small
        return false;

      ConstantRange cr = LVI->getConstantRange(v, context->getParent(), context);
      if (!cr.getSignedMin().sge(APInt::getSignedMinValue(Width)
                                 .sext(v->getType()->getIntegerBitWidth()))
       || !cr.getSignedMax().sle(APInt::getSignedMaxValue(Width)
                                 .sext(v->getType()->getIntegerBitWidth())))
        // Unable to fit in an integer of size Width
        return false;

      return (isa<BinaryOperator>(v) ||
              isa<SelectInst>(v) ||
              isa<PHINode>(v));
    }

    Instruction *convertBinaryOperator(BinaryOperator *BO, Type *target) {
      // get new operands of the required size
      Value *op0 = convertSize(BO->getOperand(0), target);
      Value *op1 = convertSize(BO->getOperand(1), target);
      return BinaryOperator::Create(BO->getOpcode(), op0, op1, BO->getName(), BO);
    }

    Instruction *convertPHINode(PHINode *P, Type *target) {
      PHINode *newP = PHINode::Create(target, P->getNumOperands(), P->getName(), P);
      for(unsigned i = 0; i < P->getNumOperands(); i++) {
        newP->addIncoming(convertSize(P->getIncomingValue(i), target),
                          P->getIncomingBlock(i));
      }
      return newP;
    }

    Instruction *convertICmp(ICmpInst *I, Type *target) {
      // get new operands of the required size
      Value *op0 = convertSize(I->getOperand(0), target);
      Value *op1 = convertSize(I->getOperand(1), target);
      return new ICmpInst(I, I->getPredicate(), op0, op1, I->getName());
    }

    Instruction *convertSelect(SelectInst *I, Type *target) {
      // get new operands of the required size
      Value *op1 = convertSize(I->getOperand(1), target);
      Value *op2 = convertSize(I->getOperand(2), target);
      return SelectInst::Create(I->getOperand(0), op1, op2, I->getName(), I);
    }

    // Generate a new instruction for i, while fulfilling our contract with users
    void convertInstruction(Instruction *i, Type *target) {
      DEBUG(dbgs() << "Instruction Before Conversion: ");
      DEBUG(i->dump());
      Instruction *newInst = i;
      if (BinaryOperator *BO = dyn_cast<BinaryOperator>(i))
        newInst = convertBinaryOperator(BO, target);
      else if (PHINode *P = dyn_cast<PHINode>(i))
        newInst = convertPHINode(P, target);
      else if (ICmpInst *CMP = dyn_cast<ICmpInst>(i))
        newInst = convertICmp(CMP, target);
      else if (SelectInst *S = dyn_cast<SelectInst>(i))
        newInst = convertSelect(S, target);

      DEBUG(dbgs() << "Instruction After Conversion: ");
      DEBUG(newInst->dump());

      // Replace all uses of the instruction with an equivalent
      Value *likeOld = convertSize(newInst, i->getType());
      DEBUG(dbgs() << "Equivalent for Users: ");
      DEBUG(likeOld->dump());
      i->replaceAllUsesWith(likeOld);
      // Remove the old instruction
      i->eraseFromParent();
    }


    // In order to avoid worrying about the number of users of a given
    // cast during the transformations, we defer cleanup until the end.
    // This function removes any casts that no longer have any users.
    bool removeDeadCasts(Function &F) {
      bool didSomething = true;
      while(didSomething) {
        didSomething = false;
        for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
          for (auto i = bb->begin(), e = bb->end(); i != e; ++i) {
            if (CastInst *cast = dyn_cast<CastInst>(i)) {
              if (cast->getNumUses() == 0) {
                DEBUG(dbgs() << "Removing dead cast: \n");
                cast->dump();
                cast->eraseFromParent();
                didSomething = true;
                break;
              }
            }
          }
        }
      }
      return didSomething;
    }

    bool runOnFunction(Function &F) override {
      LVI = &getAnalysis<LazyValueInfoWrapperPass>().getLVI();
      LLVMContext &C = F.getContext();
      Type *Int32Ty = IntegerType::getInt32Ty(C);
      Type *Int16Ty = IntegerType::getInt16Ty(C);

      bool didSomething = false;
      bool didStIter = true;
      while (didStIter) {
        didStIter = false;
        for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
          for (auto i = bb->begin(), e = bb->end(); i != e; ++i) {
            Instruction *I = &*i;
            if(canConvertToInt(16, I, I)) {
              convertInstruction(I, Int16Ty);
              didSomething = true;
              didStIter = true;
              break;
            }
            if(canConvertToInt(32, I, I)) {
              convertInstruction(I, Int32Ty);
              didSomething = true;
              didStIter = true;
              break;
            }
          }
        }
      }

      DEBUG(dbgs() << "Downcasting complete, removing dead casts\n");

      if(didSomething)
        removeDeadCasts(F);

      return didSomething;
    }
  };

  struct PrintWidth : public FunctionPass {
    static char ID;
    PrintWidth() : FunctionPass(ID) {}

    LazyValueInfo *LVI;

    void getAnalysisUsage(AnalysisUsage& AU) const override {
      AU.addRequired<LazyValueInfoWrapperPass>();
    }

    bool runOnFunction(Function &F) override {
      LVI = &getAnalysis<LazyValueInfoWrapperPass>().getLVI();
      for (auto bb = F.begin(), e = F.end(); bb != e; ++bb) {
        errs() << "In " << bb->getName() << "\n";
        for (auto i = bb->begin(), e = bb->end(); i != e; ++i) {
          if(i->getType()->isIntegerTy()) {
            ConstantRange cr = LVI->getConstantRange(&*i, &*bb, &*i);
            unsigned minWidth;
            if(cr.isFullSet()) {
              minWidth = cr.getBitWidth();
            } else {
              for (minWidth=1; minWidth <= cr.getBitWidth(); minWidth++) {
                APInt min, max;
                if (cr.getLower().isNonNegative()) {
                  max = APInt::getMaxValue(minWidth).zextOrSelf(cr.getBitWidth());
                  if(cr.getUpper().ule(max)) {
                    break;
                  }
                } else {
                  min = APInt::getSignedMinValue(minWidth).sextOrSelf(cr.getBitWidth());
                  max = APInt::getSignedMaxValue(minWidth).sextOrSelf(cr.getBitWidth());
                  if(cr.getUpper().sle(max) && cr.getLower().sge(min)) {
                    break;
                  }
                }
              }
            }
            errs()  << "i" << minWidth << "\t" << cr << "\t= " << *i << "\n";
          }
        }
      }
      return false;
    }
  };
}

char ReduceWidth::ID = 0;
static RegisterPass<ReduceWidth> X("redwidth", "Reduce integers to the smallest bitwidth possible", false, false);
static RegisterPass<PrintWidth> Y("pwidth", "Print ranges and widths for all values", false, false);
