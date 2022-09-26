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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"

/* *******Implementation Starts Here******* */
// include necessary header files
/* *******Implementation Ends Here******* */

using namespace llvm;

#define DEBUG_TYPE "fplicm"


namespace Correctness{
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
