//===-- Frequent Path Loop Invariant Code Motion Pass ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// EECS583 F22 - This pass can be used as a template for your Frequent Path LICM
//               homework assignment. The pass gets registered as "fplicm".
//
// This pass performs loop invariant code motion, attempting to remove as much
// code from the body of a loop as possible.  It does this by either hoisting
// code into the preheader block, or by sinking code to the exit blocks if it is
// safe. 
//
////===----------------------------------------------------------------------===//
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Scalar/LICM.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"

/* *******Implementation Starts Here******* */
// include necessary header files
/* *******Implementation Ends Here******* */

using namespace llvm;

#define DEBUG_TYPE "fplicm"

struct FPLICM {
  Loop* L;
  LoopInfo* LI;
  BranchProbabilityInfo* BPI;
  SmallPtrSet<BasicBlock *, 8> FrequentPath;

  FPLICM(Loop *L, LoopInfo *LI, BranchProbabilityInfo *BPI)
    : L(L), LI(LI), BPI(BPI) {
  }

  bool run() {
    LoopBlocksRPO Worklist(L);
    Worklist.perform(LI);
    // determine most likely path
    auto BB = L->getHeader();
    while (true) {
      errs() << BB->getName();
      FrequentPath.insert(BB);
      auto NextBB = getMostLikelySuccessor(BB);
      if (!NextBB) {
        errs() << " has no most likely path.\n";
        return false;
      }
      errs() << " -> " << NextBB->getName() << "\n";
      if (NextBB == L->getHeader()) {
        break;
      }
      BB = NextBB;
    }

    // traverse FreqentPath (not in order) to find invariant pointers
    // their loads should be hoisted, and their stores should be fixed-up
    // std::vector<Value *> InvariantPtrs;    
    for (BasicBlock *BB: FrequentPath) {
      errs() << BB->getName() << ":\n";
      for (Instruction &I : make_early_inc_range(*BB)) {
        if (hasAlmostInvariantOperands(&I)) {
          if (I.getOpcode() == Instruction::Load &&
              isPtrAlmostInvariant(I.getOperand(0))) {
            // InvariantPtrs.push_back(I.getOperand(0));
            I.moveBefore(L->getLoopPreheader()->getTerminator());
            I.updateLocationAfterHoist();
            SmallVector<PHINode *, 16> NewPHIs;
            SSAUpdater SSA(&NewPHIs);
            SSA.Initialize(I.getType(), "phi");
            SSA.AddAvailableValue(I.getParent(), &I);
            for (Value *user: I.getOperand(0)->users()) {
              Instruction *I = dyn_cast<Instruction>(user);
              if (I->getOpcode() == Instruction::Store) {
                SSA.AddAvailableValue(I->getParent(), I->getOperand(0));
              }
            }
            std::vector<Use *> uses;
            for (Use &use: I.uses()) {
              uses.push_back(&use);
            }
            for (auto i : uses) {
              SSA.RewriteUseAfterInsertions(*i);
            }
          }
        }
        I.print(errs());
        errs() << "\n";
      }
    }
    // Hoist and fixed-up
    // for (Value *V: InvariantPtrs) {
    //   for (Value *user: V->users()) {
    //     Instruction *I = dyn_cast<Instruction>(user);
    //     if (I->getOpcode() == Instruction::Load) {

    //     } else if (I->getOpcode() == Instruction::Store) {

    //     } else {
    //       errs() >> I->
    //     }
    //   }
    // }
    // return !InvariantPtrs.empty();
    return true;
  }

  bool isPtrAlmostInvariant(const Value *V) {
    // return if no user of V is a STORE in the frequent path
    return none_of(V->users(), [this](const Value *V) {
      if (const Instruction *I = dyn_cast<Instruction>(V))
        return I->getOpcode() == Instruction::Store &&
               FrequentPath.count(I->getParent()) != 0;
      return false; // non-instruction is not store
    });
  }

  bool isAlmostInvariant(const Value *V) {
    if (const Instruction *I = dyn_cast<Instruction>(V))
      return FrequentPath.count(I->getParent()) == 0;
    return true; // All non-instructions are loop invariant
  }

  bool hasAlmostInvariantOperands(const Instruction *I) {
    return all_of(I->operands(), [this](const Value *V) {
      return isAlmostInvariant(V);
    });
  }

  BasicBlock *getMostLikelySuccessor(const BasicBlock *BB) {
    auto I = BB->getTerminator();
    for (unsigned i = 0; i < I->getNumSuccessors(); i++) {
      const auto &Prob = BPI->getEdgeProbability(BB, i);
      if ((double) Prob.getNumerator() >= 1717986918) {
        errs() << " " << Prob.getNumerator() / ( Prob.getDenominator() / 100) << "%";
        return I->getSuccessor(i);
      }
    }
    return nullptr;
  }
};

namespace Correctness{
struct FPLICMPass : public LoopPass {
  static char ID;
  FPLICMPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    bool Changed = false;

    /* *******Implementation Starts Here******* */
    FPLICM Helper(
      L,
      &getAnalysis<LoopInfoWrapperPass>().getLoopInfo(),
      &getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI()
    );
    Changed = Helper.run();
    /* *******Implementation Ends Here******* */
    
    return Changed;
  }


  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<BranchProbabilityInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
  }

private:
  /// Little predicate that returns true if the specified basic block is in
  /// a subloop of the current one, not the current one itself.
  bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {
    assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
    return LI->getLoopFor(BB) != CurLoop;
  }

};
} // end of namespace Correctness

char Correctness::FPLICMPass::ID = 0;
static RegisterPass<Correctness::FPLICMPass> X("fplicm-correctness", "Frequent Loop Invariant Code Motion for correctness test", false, false);


namespace Performance{
struct FPLICMPass : public LoopPass {
  static char ID;
  FPLICMPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    bool Changed = false;

    /* *******Implementation Starts Here******* */
    

    /* *******Implementation Ends Here******* */
    
    return Changed;
  }


  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<BranchProbabilityInfoWrapperPass>();
    AU.addRequired<BlockFrequencyInfoWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
  }

private:
  /// Little predicate that returns true if the specified basic block is in
  /// a subloop of the current one, not the current one itself.
  bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {
    assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
    return LI->getLoopFor(BB) != CurLoop;
  }

}; 
} // end of namespace Performance

char Performance::FPLICMPass::ID = 0;
static RegisterPass<Performance::FPLICMPass> Y("fplicm-performance", "Frequent Loop Invariant Code Motion for performance test", false, false);
