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
    std::vector<Instruction *> AllHoisted;
    std::vector<Instruction *> LoadHoisted;
    for (BasicBlock *BB: FrequentPath) {
      errs() << BB->getName() << ":\n";
      for (Instruction &I : make_early_inc_range(*BB)) {
        if (hasAlmostInvariantOperands(&I)) {
          if (I.getOpcode() == Instruction::Load && isPtrAlmostInvariant(cast<LoadInst>(&I)->getPointerOperand())) {
            errs() << "HOISTING >>>";
            // hoist loads from almost invariant mem
            I.moveBefore(L->getLoopPreheader()->getTerminator());
            I.updateLocationAfterHoist();
            LoadHoisted.push_back(&I);
            AllHoisted.push_back(&I);
          } else if (I.getOpcode() == Instruction::Store && isMSSA(cast<StoreInst>(&I))) {
            // errs() << "HOISTING >>>";
            // // hoist MSSA stores
            // I.moveBefore(L->getLoopPreheader()->getTerminator());
            // I.updateLocationAfterHoist();
            // AllHoisted.push_back(&I);
          } else if (canHoist(I)) {
            // hoist any non-memory operations
            errs() << "HOISTING >>>";
            I.moveBefore(L->getLoopPreheader()->getTerminator());
            I.updateLocationAfterHoist();
            AllHoisted.push_back(&I);

          }
        }
        I.print(errs());
        errs() << "\n";
      }
    }

    std::vector<Instruction *> Fixups;
    for (auto LI : LoadHoisted) {
      SmallVector<PHINode *, 16> NewPHIs;
      SSAUpdater SSA(&NewPHIs);
      SSA.Initialize(LI->getType(), "phi");
      // collect loaded value
      SSA.AddAvailableValue(LI->getParent(), LI);
      // for all stores breaking the hoisted load
      for (Value *user: LI->getOperand(0)->users()) {
        Instruction *I = dyn_cast<Instruction>(user);
        if (I->getOpcode() == Instruction::Store && L->contains(I)) {
          // collect stored value
          SSA.AddAvailableValue(I->getParent(), I->getOperand(0));
          // insert subsequent fixup
          ValueToValueMapTy vmap;
          auto *InsertPos = I->getNextNode();
          for (auto HI : AllHoisted) {
            auto *FI = HI->clone(); // fixup instruction
            FI->insertBefore(InsertPos);
            vmap[HI] = FI;
            RemapInstruction(FI, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
          }
          Fixups.push_back(I->getNextNode());
        }
      }
      // resolve phi for all uses of LI
      std::vector<Use *> uses;
      for (Use &use: LI->uses()) {
        uses.push_back(&use);
      }
      for (auto i : uses) {
        SSA.RewriteUseAfterInsertions(*i);
      }
    }

    for (auto HI : AllHoisted) {
      errs() << "SSA >>>";
      HI->print(errs());
      errs() << "\n";
      // ignore stores
      if (HI->getOpcode() == Instruction::Store) {
        for (auto & FI : Fixups) FI = FI->getNextNode();
        continue;
      }
      SmallVector<PHINode *, 16> NewPHIs;
      SSAUpdater SSA(&NewPHIs);
      SSA.Initialize(HI->getType(), "phi");
      SSA.AddAvailableValue(HI->getParent(), HI);
      for (auto & FI : Fixups) {
        SSA.AddAvailableValue(FI->getParent(), FI);
        FI = FI->getNextNode();
      }
      // resolve phi for all uses of HI
      std::vector<Use *> uses;
      for (Use &use: HI->uses()) {
        uses.push_back(&use);
      }
      for (auto i : uses) {
        SSA.RewriteUseAfterInsertions(*i);
      }
    }

    // // get the depents of every hoisted LI
    // for (auto & [Dependent, LIs] : invariantDependencies) {
    //   for (auto & LI : LIs) {
    //     invariantDependents[LI].push_back(Dependent);
    //   }
    // }
    // for (auto & [I, Dependents] : invariantDependents) {
    //   SmallVector<PHINode *, 16> NewPHIs;
    //   SSAUpdater SSA(&NewPHIs);
    //   SSA.Initialize(I->getType(), "phi");
    //   // collect the initially loaded value
    //   SSA.AddAvailableValue(I->getParent(), I);
    //   // find all stores and collect the stored values
    //   for (Value *user: I->getOperand(0)->users()) {
    //     Instruction *I = dyn_cast<Instruction>(user);
    //     if (I->getOpcode() == Instruction::Store) {
    //       SSA.AddAvailableValue(I->getParent(), I->getOperand(0));
    //     }
    //   }
    //   fixupUses(I, SSA);
    //   for (auto & D : Dependents) {
    //     errs() << "Fixing >>>";
    //     D->print(errs());
    //     errs() << "\n";
    //     SmallVector<PHINode *, 16> NewPHIs;
    //     SSAUpdater SSA(&NewPHIs);
    //     SSA.Initialize(D->getType(), "phi");
    //     // collect the initially loaded value
    //     SSA.AddAvailableValue(D->getParent(), D);
    //     // clone dependent calculation for fixup
    //     for (Value *user: I->getOperand(0)->users()) {
    //       // Instruction *I = dyn_cast<Instruction>(user);
    //       // if (I->getOpcode() == Instruction::Store) {
    //       //   SSA.AddAvailableValue(I->getParent(), I->getOperand(0));
    //       // }
    //       Instruction *Fixup = D->clone();
    //       Fixup->insertAfter(dyn_cast<Instruction>(user));
    //       SSA.AddAvailableValue(Fixup->getParent(), Fixup);
    //     }
    //     fixupUses(D, SSA);
    //   }
    // }

    errs() << "\n\nNow:\n";
    for (Instruction &I : *(L->getLoopPreheader())) {
      I.print(errs());
      errs() << "\n";
    }
    for (BasicBlock *BB: Worklist) {
      errs() << BB->getName() << ":\n";
      for (Instruction &I : *BB) {
        I.print(errs());
        errs() << "\n";
      }
    }
    return true;
  }

  void fixupUses(Value *V, SSAUpdater &SSA) {
    std::vector<Use *> uses;
    for (Use &use: V->uses()) {
      uses.push_back(&use);
    }
    for (auto i : uses) {
      SSA.RewriteUseAfterInsertions(*i);
    }
  }

  // void addDependentInvariant(Instruction *I) {
  //   invariantDependencies.insert({I, {}});
  //   auto &Dependencies = invariantDependencies[I];
  //   for (int i = 0; i < I->getNumOperands(); i++) {
  //     auto &D = invariantDependencies[dyn_cast<Instruction>(I->getOperand(i))];
  //     Dependencies.insert(Dependencies.end(), D.begin(), D.end());
  //   }
  // }

  bool isPtrAlmostInvariant(const Value *Ptr) {
    // return if no user of V is a store in the frequent path
    return none_of(Ptr->users(), [this](const Value *V) {
      if (const Instruction *I = dyn_cast<Instruction>(V))
        return I->getOpcode() == Instruction::Store &&
               FrequentPath.count(I->getParent()) != 0;
      return false; // non-instruction is not store
    });
  }

  bool isMSSA(const StoreInst *SI) {
    // return if Ptr is stored only once
    return none_of(SI->getPointerOperand()->users(), [&](const Value *V) {
      // return if V is used in another store
      if (const Instruction *I = dyn_cast<Instruction>(V))
        return I->getOpcode() == Instruction::Store && I != SI;
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

  bool canHoist(Instruction &I) {
    switch (I.getOpcode()) {
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
    case Instruction::ICmp:
    case Instruction::SRem:
    case Instruction::FAdd:
    case Instruction::FSub:
    case Instruction::FMul:
    case Instruction::FDiv:
    case Instruction::FRem:
    case Instruction::FCmp:
    case Instruction::GetElementPtr:
    case Instruction::SExt:
    case Instruction::Call:
        return true;
    default:
        return false;
    }
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
