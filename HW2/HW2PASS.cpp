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
#include <unordered_map>
#include <unordered_set>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Support/Format.h"
#include "llvm/IR/Instruction.def"

using namespace llvm;

namespace {

struct SESSA : public FunctionPass {
  static char ID;
  SESSA() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    for (auto & I : F.getEntryBlock().getInstList()) {
      if (AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
        if (isAllocaPromotable(AI)) allocas.insert(AI);
      }
    }
    if (allocas.empty()) return false;
    for (auto & BB : F.getBasicBlockList()) {
      for (auto & I : make_early_inc_range(BB)) {
        if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
          if (allocas.find(SI->getPointerOperand()) != allocas.end()) {
            errs() << "promoting: ";
            I.print(errs());
            errs() << "\n";
            writeVariable(SI->getPointerOperand(), SI->getParent(), SI->getValueOperand());
            SI->eraseFromParent();
          }
        } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
          if (allocas.find(LI->getPointerOperand()) != allocas.end()) {
            errs() << "promoting: ";
            I.print(errs());
            errs() << "\n";
            Value* def = readVariable(LI->getPointerOperand(), LI->getParent());
            LI->replaceAllUsesWith(def);
            LI->eraseFromParent();
          }
        }
      }
      for (BasicBlock* S : successors(&BB)) {
        if (predCount.find(S) == predCount.end()) {
          predCount[S] = pred_size(S);
        }
        predCount[S]--;
        if (predCount[S] == 0) {
          sealBlock(S);
        }
      }
    }
    for (Value* V : allocas) {
      cast<Instruction>(V)->eraseFromParent();
    }
    errs() << "result:\n";
    for (auto & BB : F.getBasicBlockList()) {
      for (auto & I : make_early_inc_range(BB)) {
        I.print(errs());
        errs() << "\n";
      }
    }
    return true;
  }

  void writeVariable(Value* variable, BasicBlock* block, Value* value) {
    currentDef[variable][block] = value;
  }

  Value* readVariable(Value* variable, BasicBlock* block) {
    if (currentDef[variable].find(block) != currentDef[variable].end()) {
      // local value numbering
      return currentDef[variable][block];
    }
    // global value numbering
    return readVariableRecursive(variable, block);
  }

  Value* readVariableRecursive(Value* variable, BasicBlock* block) {
    Value* val;
    if (sealedBlocks.find(block) == sealedBlocks.end()) {
      // Incomplete CFG
      val = newPhi(cast<AllocaInst>(variable)->getAllocatedType(), block);
      incompletePhis[block][variable] = val;
    } else if (pred_size(block) == 1) {
      // Optimize the common case of one predecessor: No phi needed
      val = readVariable(variable, *pred_begin(block));
    } else {
      // Break potential cycles with operandless phi
      val = newPhi(cast<AllocaInst>(variable)->getAllocatedType(), block);
      writeVariable(variable, block, val);
      val = addPhiOperands(variable, cast<PHINode>(val));
    }
    writeVariable(variable, block, val);
    return val;
  }

  Value* addPhiOperands(Value* variable, PHINode* phi) {
    // Determine operands from predecessors
    for (llvm::BasicBlock* pred : predecessors(phi->getParent())) {
      phi->addIncoming(readVariable(variable, pred), pred);
    }
    return phi;
  }

  Value* newPhi(Type* type, BasicBlock* block) {
    std::string name = "phi" + std::to_string(numPHINodes);
    return PHINode::Create(type, 0, name, &block->front());
  }

  void sealBlock(BasicBlock* block) {
    for (auto & p : incompletePhis[block]) {
      auto [variable, phi] = p;
      addPhiOperands(variable, cast<PHINode>(phi));
    }
    sealedBlocks.insert(block);
  }

  std::unordered_set<Value*> allocas;
  std::unordered_map<BasicBlock*, std::unordered_map<Value*, Value*>> incompletePhis;
  std::unordered_map<Value*, std::unordered_map<BasicBlock*, Value*>> currentDef;
  std::unordered_set<BasicBlock*> sealedBlocks;
  std::unordered_map<BasicBlock*, unsigned> predCount;
  unsigned numPHINodes = 0;

}; // end of struct SESSA

}  // end of anonymous namespace

char SESSA::ID = 0;
static RegisterPass<SESSA> X("sessa", "SESSA World Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);