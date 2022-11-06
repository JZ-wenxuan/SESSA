#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
 #include "llvm/ADT/ArrayRef.h"
 #include "llvm/ADT/DenseMap.h"
 #include "llvm/ADT/STLExtras.h"
 #include "llvm/ADT/SmallPtrSet.h"
 #include "llvm/ADT/SmallVector.h"
 #include "llvm/ADT/Statistic.h"
 #include "llvm/ADT/Twine.h"
 #include "llvm/Analysis/AssumptionCache.h"
 #include "llvm/Analysis/InstructionSimplify.h"
 #include "llvm/Analysis/IteratedDominanceFrontier.h"
 #include "llvm/Analysis/ValueTracking.h"
 #include "llvm/IR/BasicBlock.h"
 #include "llvm/IR/CFG.h"
 #include "llvm/IR/Constant.h"
 #include "llvm/IR/Constants.h"
 #include "llvm/IR/DIBuilder.h"
 #include "llvm/IR/DebugInfo.h"
 #include "llvm/IR/Dominators.h"
 #include "llvm/IR/Function.h"
 #include "llvm/IR/InstrTypes.h"
 #include "llvm/IR/Instruction.h"
 #include "llvm/IR/Instructions.h"
 #include "llvm/IR/IntrinsicInst.h"
 #include "llvm/IR/Intrinsics.h"
 #include "llvm/IR/LLVMContext.h"
 #include "llvm/IR/Module.h"
 #include "llvm/IR/Type.h"
 #include "llvm/IR/User.h"
 #include "llvm/Support/Casting.h"
 #include "llvm/Transforms/Utils/Local.h"
 #include "llvm/Transforms/Utils/PromoteMemToReg.h"
 #include <algorithm>
 #include <cassert>
 #include <iterator>
 #include <utility>
 #include <vector>

using namespace llvm;

namespace {

bool isAllocaPromotable(const AllocaInst *AI) {
  // Only allow direct and non-volatile loads and stores...
  for (const User *U : AI->users()) {
    if (const LoadInst *LI = dyn_cast<LoadInst>(U)) {
      // Note that atomic loads can be transformed; atomic semantics do
      // not have any meaning for a local alloca.
      if (LI->isVolatile() || LI->getType() != AI->getAllocatedType())
        return false;
    } else if (const StoreInst *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getValueOperand() == AI ||
          SI->getValueOperand()->getType() != AI->getAllocatedType())
        return false; // Don't allow a store OF the AI, only INTO the AI.
      // Note that atomic stores can be transformed; atomic semantics do
      // not have any meaning for a local alloca.
      if (SI->isVolatile())
        return false;
    } else if (const IntrinsicInst *II = dyn_cast<IntrinsicInst>(U)) {
      if (!II->isLifetimeStartOrEnd() && !II->isDroppable())
        return false;
    } else if (const BitCastInst *BCI = dyn_cast<BitCastInst>(U)) {
      if (!onlyUsedByLifetimeMarkersOrDroppableInsts(BCI))
        return false;
    } else if (const GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(U)) {
      if (!GEPI->hasAllZeroIndices())
        return false;
      if (!onlyUsedByLifetimeMarkersOrDroppableInsts(GEPI))
        return false;
    } else if (const AddrSpaceCastInst *ASCI = dyn_cast<AddrSpaceCastInst>(U)) {
      if (!onlyUsedByLifetimeMarkers(ASCI))
        return false;
    } else {
      return false;
    }
  }

  return true;
}

struct SESSA : public FunctionPass {
  static char ID;
  SESSA() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    errs() << "SESSA: ";
    errs().write_escaped(F.getName()) << '\n';
    return false;
  }
}; // end of struct SESSA

}  // end of anonymous namespace

char SESSA::ID = 0;
static RegisterPass<SESSA> X("sessa", "SESSA World Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);