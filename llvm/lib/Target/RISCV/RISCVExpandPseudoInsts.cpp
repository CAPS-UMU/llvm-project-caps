//===-- RISCVExpandPseudoInsts.cpp - Expand pseudo instructions -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains a pass that expands pseudo instructions into target
// instructions. This pass should be run after register allocation but before
// the post-regalloc scheduling pass.
//
//===----------------------------------------------------------------------===//

#include "RISCV.h"
#include "RISCVInstrInfo.h"
#include "RISCVTargetMachine.h"

#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/MC/MCContext.h"

using namespace llvm;

#define DEBUG_TYPE "riscv-expand-pseudo" 

#define RISCV_EXPAND_PSEUDO_NAME "RISC-V pseudo instruction expansion pass"
#define RISCV_PRERA_EXPAND_PSEUDO_NAME "RISC-V Pre-RA pseudo instruction expansion pass"

namespace {

class RISCVExpandPseudo : public MachineFunctionPass {
public:
  const RISCVSubtarget *STI;
  const RISCVInstrInfo *TII;
  static char ID;

  RISCVExpandPseudo() : MachineFunctionPass(ID) {}

  bool runOnMachineFunction(MachineFunction &MF) override;

  StringRef getPassName() const override { return RISCV_EXPAND_PSEUDO_NAME; }

private:
  bool expandMBB(MachineBasicBlock &MBB);
  bool expandMI(MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
                MachineBasicBlock::iterator &NextMBBI);
  bool expandCCOp(MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
                  MachineBasicBlock::iterator &NextMBBI);
  bool expandVSetVL(MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI);
  bool expandVMSET_VMCLR(MachineBasicBlock &MBB,
                         MachineBasicBlock::iterator MBBI, unsigned Opcode);
  bool expandRV32ZdinxStore(MachineBasicBlock &MBB,
                            MachineBasicBlock::iterator MBBI);
  bool expandRV32ZdinxLoad(MachineBasicBlock &MBB,
                           MachineBasicBlock::iterator MBBI);
#ifndef NDEBUG
  unsigned getInstSizeInBytes(const MachineFunction &MF) const {
    unsigned Size = 0;
    for (auto &MBB : MF)
      for (auto &MI : MBB)
        Size += TII->getInstSizeInBytes(MI);
    return Size;
  }
#endif
};

char RISCVExpandPseudo::ID = 0;

bool RISCVExpandPseudo::runOnMachineFunction(MachineFunction &MF) {
  STI = &MF.getSubtarget<RISCVSubtarget>();
  TII = STI->getInstrInfo();

#ifndef NDEBUG
  const unsigned OldSize = getInstSizeInBytes(MF);
#endif

  bool Modified = false;
  for (auto &MBB : MF)
    Modified |= expandMBB(MBB);

#ifndef NDEBUG
  const unsigned NewSize = getInstSizeInBytes(MF);
  assert(OldSize >= NewSize);
#endif
  return Modified;
}

bool RISCVExpandPseudo::expandMBB(MachineBasicBlock &MBB) {
  bool Modified = false;

  MachineBasicBlock::iterator MBBI = MBB.begin(), E = MBB.end();
  while (MBBI != E) {
    MachineBasicBlock::iterator NMBBI = std::next(MBBI);
    Modified |= expandMI(MBB, MBBI, NMBBI);
    MBBI = NMBBI;
  }

  return Modified;
}

bool RISCVExpandPseudo::expandMI(MachineBasicBlock &MBB,
                                 MachineBasicBlock::iterator MBBI,
                                 MachineBasicBlock::iterator &NextMBBI) {
  // RISCVInstrInfo::getInstSizeInBytes expects that the total size of the
  // expanded instructions for each pseudo is correct in the Size field of the
  // tablegen definition for the pseudo.
  switch (MBBI->getOpcode()) {
  case RISCV::PseudoRV32ZdinxSD:
    return expandRV32ZdinxStore(MBB, MBBI);
  case RISCV::PseudoRV32ZdinxLD:
    return expandRV32ZdinxLoad(MBB, MBBI);
  case RISCV::PseudoCCMOVGPR:
  case RISCV::PseudoCCADD:
  case RISCV::PseudoCCSUB:
  case RISCV::PseudoCCAND:
  case RISCV::PseudoCCOR:
  case RISCV::PseudoCCXOR:
  case RISCV::PseudoCCADDW:
  case RISCV::PseudoCCSUBW:
  case RISCV::PseudoCCSLL:
  case RISCV::PseudoCCSRL:
  case RISCV::PseudoCCSRA:
  case RISCV::PseudoCCADDI:
  case RISCV::PseudoCCSLLI:
  case RISCV::PseudoCCSRLI:
  case RISCV::PseudoCCSRAI:
  case RISCV::PseudoCCANDI:
  case RISCV::PseudoCCORI:
  case RISCV::PseudoCCXORI:
  case RISCV::PseudoCCSLLW:
  case RISCV::PseudoCCSRLW:
  case RISCV::PseudoCCSRAW:
  case RISCV::PseudoCCADDIW:
  case RISCV::PseudoCCSLLIW:
  case RISCV::PseudoCCSRLIW:
  case RISCV::PseudoCCSRAIW:
    return expandCCOp(MBB, MBBI, NextMBBI);
  case RISCV::PseudoVSETVLI:
  case RISCV::PseudoVSETVLIX0:
  case RISCV::PseudoVSETIVLI:
    return expandVSetVL(MBB, MBBI);
  case RISCV::PseudoVMCLR_M_B1:
  case RISCV::PseudoVMCLR_M_B2:
  case RISCV::PseudoVMCLR_M_B4:
  case RISCV::PseudoVMCLR_M_B8:
  case RISCV::PseudoVMCLR_M_B16:
  case RISCV::PseudoVMCLR_M_B32:
  case RISCV::PseudoVMCLR_M_B64:
    // vmclr.m vd => vmxor.mm vd, vd, vd
    return expandVMSET_VMCLR(MBB, MBBI, RISCV::VMXOR_MM);
  case RISCV::PseudoVMSET_M_B1:
  case RISCV::PseudoVMSET_M_B2:
  case RISCV::PseudoVMSET_M_B4:
  case RISCV::PseudoVMSET_M_B8:
  case RISCV::PseudoVMSET_M_B16:
  case RISCV::PseudoVMSET_M_B32:
  case RISCV::PseudoVMSET_M_B64:
    // vmset.m vd => vmxnor.mm vd, vd, vd
    return expandVMSET_VMCLR(MBB, MBBI, RISCV::VMXNOR_MM);
  }

  return false;
}

bool RISCVExpandPseudo::expandCCOp(MachineBasicBlock &MBB,
                                   MachineBasicBlock::iterator MBBI,
                                   MachineBasicBlock::iterator &NextMBBI) {

  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();

  MachineBasicBlock *TrueBB = MF->CreateMachineBasicBlock(MBB.getBasicBlock());
  MachineBasicBlock *MergeBB = MF->CreateMachineBasicBlock(MBB.getBasicBlock());

  MF->insert(++MBB.getIterator(), TrueBB);
  MF->insert(++TrueBB->getIterator(), MergeBB);

  // We want to copy the "true" value when the condition is true which means
  // we need to invert the branch condition to jump over TrueBB when the
  // condition is false.
  auto CC = static_cast<RISCVCC::CondCode>(MI.getOperand(3).getImm());
  CC = RISCVCC::getOppositeBranchCondition(CC);

  // Insert branch instruction.
  BuildMI(MBB, MBBI, DL, TII->getBrCond(CC))
      .addReg(MI.getOperand(1).getReg())
      .addReg(MI.getOperand(2).getReg())
      .addMBB(MergeBB);

  Register DestReg = MI.getOperand(0).getReg();
  assert(MI.getOperand(4).getReg() == DestReg);

  if (MI.getOpcode() == RISCV::PseudoCCMOVGPR) {
    // Add MV.
    BuildMI(TrueBB, DL, TII->get(RISCV::ADDI), DestReg)
        .add(MI.getOperand(5))
        .addImm(0);
  } else {
    unsigned NewOpc;
    switch (MI.getOpcode()) {
    default:
      llvm_unreachable("Unexpected opcode!");
    case RISCV::PseudoCCADD:   NewOpc = RISCV::ADD;   break;
    case RISCV::PseudoCCSUB:   NewOpc = RISCV::SUB;   break;
    case RISCV::PseudoCCSLL:   NewOpc = RISCV::SLL;   break;
    case RISCV::PseudoCCSRL:   NewOpc = RISCV::SRL;   break;
    case RISCV::PseudoCCSRA:   NewOpc = RISCV::SRA;   break;
    case RISCV::PseudoCCAND:   NewOpc = RISCV::AND;   break;
    case RISCV::PseudoCCOR:    NewOpc = RISCV::OR;    break;
    case RISCV::PseudoCCXOR:   NewOpc = RISCV::XOR;   break;
    case RISCV::PseudoCCADDI:  NewOpc = RISCV::ADDI;  break;
    case RISCV::PseudoCCSLLI:  NewOpc = RISCV::SLLI;  break;
    case RISCV::PseudoCCSRLI:  NewOpc = RISCV::SRLI;  break;
    case RISCV::PseudoCCSRAI:  NewOpc = RISCV::SRAI;  break;
    case RISCV::PseudoCCANDI:  NewOpc = RISCV::ANDI;  break;
    case RISCV::PseudoCCORI:   NewOpc = RISCV::ORI;   break;
    case RISCV::PseudoCCXORI:  NewOpc = RISCV::XORI;  break;
    case RISCV::PseudoCCADDW:  NewOpc = RISCV::ADDW;  break;
    case RISCV::PseudoCCSUBW:  NewOpc = RISCV::SUBW;  break;
    case RISCV::PseudoCCSLLW:  NewOpc = RISCV::SLLW;  break;
    case RISCV::PseudoCCSRLW:  NewOpc = RISCV::SRLW;  break;
    case RISCV::PseudoCCSRAW:  NewOpc = RISCV::SRAW;  break;
    case RISCV::PseudoCCADDIW: NewOpc = RISCV::ADDIW; break;
    case RISCV::PseudoCCSLLIW: NewOpc = RISCV::SLLIW; break;
    case RISCV::PseudoCCSRLIW: NewOpc = RISCV::SRLIW; break;
    case RISCV::PseudoCCSRAIW: NewOpc = RISCV::SRAIW; break;
    }
    BuildMI(TrueBB, DL, TII->get(NewOpc), DestReg)
        .add(MI.getOperand(5))
        .add(MI.getOperand(6));
  }

  TrueBB->addSuccessor(MergeBB);

  MergeBB->splice(MergeBB->end(), &MBB, MI, MBB.end());
  MergeBB->transferSuccessors(&MBB);

  MBB.addSuccessor(TrueBB);
  MBB.addSuccessor(MergeBB);

  NextMBBI = MBB.end();
  MI.eraseFromParent();

  // Make sure live-ins are correctly attached to this new basic block.
  LivePhysRegs LiveRegs;
  computeAndAddLiveIns(LiveRegs, *TrueBB);
  computeAndAddLiveIns(LiveRegs, *MergeBB);

  return true;
}

bool RISCVExpandPseudo::expandVSetVL(MachineBasicBlock &MBB,
                                     MachineBasicBlock::iterator MBBI) {
  assert(MBBI->getNumExplicitOperands() == 3 && MBBI->getNumOperands() >= 5 &&
         "Unexpected instruction format");

  DebugLoc DL = MBBI->getDebugLoc();

  assert((MBBI->getOpcode() == RISCV::PseudoVSETVLI ||
          MBBI->getOpcode() == RISCV::PseudoVSETVLIX0 ||
          MBBI->getOpcode() == RISCV::PseudoVSETIVLI) &&
         "Unexpected pseudo instruction");
  unsigned Opcode;
  if (MBBI->getOpcode() == RISCV::PseudoVSETIVLI)
    Opcode = RISCV::VSETIVLI;
  else
    Opcode = RISCV::VSETVLI;
  const MCInstrDesc &Desc = TII->get(Opcode);
  assert(Desc.getNumOperands() == 3 && "Unexpected instruction format");

  Register DstReg = MBBI->getOperand(0).getReg();
  bool DstIsDead = MBBI->getOperand(0).isDead();
  BuildMI(MBB, MBBI, DL, Desc)
      .addReg(DstReg, RegState::Define | getDeadRegState(DstIsDead))
      .add(MBBI->getOperand(1))  // VL
      .add(MBBI->getOperand(2)); // VType

  MBBI->eraseFromParent(); // The pseudo instruction is gone now.
  return true;
}

bool RISCVExpandPseudo::expandVMSET_VMCLR(MachineBasicBlock &MBB,
                                          MachineBasicBlock::iterator MBBI,
                                          unsigned Opcode) {
  DebugLoc DL = MBBI->getDebugLoc();
  Register DstReg = MBBI->getOperand(0).getReg();
  const MCInstrDesc &Desc = TII->get(Opcode);
  BuildMI(MBB, MBBI, DL, Desc, DstReg)
      .addReg(DstReg, RegState::Undef)
      .addReg(DstReg, RegState::Undef);
  MBBI->eraseFromParent(); // The pseudo instruction is gone now.
  return true;
}

// This function expands the PseudoRV32ZdinxSD for storing a double-precision
// floating-point value into memory by generating an equivalent instruction
// sequence for RV32.
bool RISCVExpandPseudo::expandRV32ZdinxStore(MachineBasicBlock &MBB,
                                             MachineBasicBlock::iterator MBBI) {
  DebugLoc DL = MBBI->getDebugLoc();
  const TargetRegisterInfo *TRI = STI->getRegisterInfo();
  Register Lo = TRI->getSubReg(MBBI->getOperand(0).getReg(), RISCV::sub_32);
  Register Hi = TRI->getSubReg(MBBI->getOperand(0).getReg(), RISCV::sub_32_hi);
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SW))
      .addReg(Lo, getKillRegState(MBBI->getOperand(0).isKill()))
      .addReg(MBBI->getOperand(1).getReg())
      .add(MBBI->getOperand(2));
  if (MBBI->getOperand(2).isGlobal() || MBBI->getOperand(2).isCPI()) {
    // FIXME: Zdinx RV32 can not work on unaligned memory.
    assert(!STI->hasFastUnalignedAccess());

    assert(MBBI->getOperand(2).getOffset() % 8 == 0);
    MBBI->getOperand(2).setOffset(MBBI->getOperand(2).getOffset() + 4);
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::SW))
        .addReg(Hi, getKillRegState(MBBI->getOperand(0).isKill()))
        .add(MBBI->getOperand(1))
        .add(MBBI->getOperand(2));
  } else {
    assert(isInt<12>(MBBI->getOperand(2).getImm() + 4));
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::SW))
        .addReg(Hi, getKillRegState(MBBI->getOperand(0).isKill()))
        .add(MBBI->getOperand(1))
        .addImm(MBBI->getOperand(2).getImm() + 4);
  }
  MBBI->eraseFromParent();
  return true;
}

// This function expands PseudoRV32ZdinxLoad for loading a double-precision
// floating-point value from memory into an equivalent instruction sequence for
// RV32.
bool RISCVExpandPseudo::expandRV32ZdinxLoad(MachineBasicBlock &MBB,
                                            MachineBasicBlock::iterator MBBI) {
  DebugLoc DL = MBBI->getDebugLoc();
  const TargetRegisterInfo *TRI = STI->getRegisterInfo();
  Register Lo = TRI->getSubReg(MBBI->getOperand(0).getReg(), RISCV::sub_32);
  Register Hi = TRI->getSubReg(MBBI->getOperand(0).getReg(), RISCV::sub_32_hi);

  // If the register of operand 1 is equal to the Lo register, then swap the
  // order of loading the Lo and Hi statements.
  bool IsOp1EqualToLo = Lo == MBBI->getOperand(1).getReg();
  // Order: Lo, Hi
  if (!IsOp1EqualToLo) {
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::LW), Lo)
        .addReg(MBBI->getOperand(1).getReg())
        .add(MBBI->getOperand(2));
  }

  if (MBBI->getOperand(2).isGlobal() || MBBI->getOperand(2).isCPI()) {
    auto Offset = MBBI->getOperand(2).getOffset();
    assert(MBBI->getOperand(2).getOffset() % 8 == 0);
    MBBI->getOperand(2).setOffset(Offset + 4);
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::LW), Hi)
        .addReg(MBBI->getOperand(1).getReg())
        .add(MBBI->getOperand(2));
    MBBI->getOperand(2).setOffset(Offset);
  } else {
    assert(isInt<12>(MBBI->getOperand(2).getImm() + 4));
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::LW), Hi)
        .addReg(MBBI->getOperand(1).getReg())
        .addImm(MBBI->getOperand(2).getImm() + 4);
  }

  // Order: Hi, Lo
  if (IsOp1EqualToLo) {
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::LW), Lo)
        .addReg(MBBI->getOperand(1).getReg())
        .add(MBBI->getOperand(2));
  }

  MBBI->eraseFromParent();
  return true;
}

class RISCVPreRAExpandPseudo : public MachineFunctionPass {
public:
  const RISCVSubtarget *STI;
  const RISCVInstrInfo *TII;
  static char ID;

  RISCVPreRAExpandPseudo() : MachineFunctionPass(ID) {}

  bool runOnMachineFunction(MachineFunction &MF) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    MachineFunctionPass::getAnalysisUsage(AU);
  }
  StringRef getPassName() const override {
    return RISCV_PRERA_EXPAND_PSEUDO_NAME;
  }

private:
  bool expandMBB(MachineBasicBlock &MBB);
  bool expandMI(MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
                MachineBasicBlock::iterator &NextMBBI);
  bool expandAuipcInstPair(MachineBasicBlock &MBB,
                           MachineBasicBlock::iterator MBBI,
                           MachineBasicBlock::iterator &NextMBBI,
                           unsigned FlagsHi, unsigned SecondOpcode);
  bool expandLoadLocalAddress(MachineBasicBlock &MBB,
                              MachineBasicBlock::iterator MBBI,
                              MachineBasicBlock::iterator &NextMBBI);
  bool expandFULDInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFULWInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUSDInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUSWInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUSHInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUSBInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUFLWInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUFSWInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUFLDInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFUFSDInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFULWUInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFULHInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFULHUInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFULBInstPair(MachineBasicBlock &MBB,
                          MachineBasicBlock::iterator MBBI,
                          MachineBasicBlock::iterator &NextMBBI);
  bool expandFULBUInstPair(MachineBasicBlock &MBB,
                           MachineBasicBlock::iterator MBBI,
                           MachineBasicBlock::iterator &NextMBBI);
  bool expandLoadGlobalAddress(MachineBasicBlock &MBB,
                               MachineBasicBlock::iterator MBBI,
                               MachineBasicBlock::iterator &NextMBBI);
  bool expandLoadTLSIEAddress(MachineBasicBlock &MBB,
                              MachineBasicBlock::iterator MBBI,
                              MachineBasicBlock::iterator &NextMBBI);
  bool expandLoadTLSGDAddress(MachineBasicBlock &MBB,
                              MachineBasicBlock::iterator MBBI,
                              MachineBasicBlock::iterator &NextMBBI);
#ifndef NDEBUG
  unsigned getInstSizeInBytes(const MachineFunction &MF) const {
    unsigned Size = 0;
    for (auto &MBB : MF)
      for (auto &MI : MBB)
        Size += TII->getInstSizeInBytes(MI);
    return Size;
  }
#endif
};

char RISCVPreRAExpandPseudo::ID = 0;

bool RISCVPreRAExpandPseudo::runOnMachineFunction(MachineFunction &MF) {
  STI = &MF.getSubtarget<RISCVSubtarget>();
  TII = STI->getInstrInfo();

#ifndef NDEBUG
  const unsigned OldSize = getInstSizeInBytes(MF);
#endif

  bool Modified = false;
  for (auto &MBB : MF)
    Modified |= expandMBB(MBB);

#ifndef NDEBUG
  const unsigned NewSize = getInstSizeInBytes(MF);
  // assert(OldSize >= NewSize);
#endif
  return Modified;
}

bool RISCVPreRAExpandPseudo::expandMBB(MachineBasicBlock &MBB) {
  bool Modified = false;

  MachineBasicBlock::iterator MBBI = MBB.begin(), E = MBB.end();
  while (MBBI != E) {
    MachineBasicBlock::iterator NMBBI = std::next(MBBI);
    Modified |= expandMI(MBB, MBBI, NMBBI);
    MBBI = NMBBI;
  }

  return Modified;
}

bool RISCVPreRAExpandPseudo::expandMI(MachineBasicBlock &MBB,
                                      MachineBasicBlock::iterator MBBI,
                                      MachineBasicBlock::iterator &NextMBBI) {

  switch (MBBI->getOpcode()) {
  case RISCV::PseudoLLA:
    return expandLoadLocalAddress(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULD:
    return expandFULDInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULW:
    return expandFULWInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUSD:
    return expandFUSDInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUSW:
    return expandFUSWInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUFLD:
    return expandFUFLDInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUFSD:
    return expandFUFSDInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUFLW:
    return expandFUFLWInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUSB:
    return expandFUSBInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUSH:
    return expandFUSHInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULWU:
    return expandFULWUInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULH:
    return expandFULHInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULHU:
    return expandFULHUInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULB:
    return expandFULBInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFULBU:
    return expandFULBUInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoFUFSW:
    return expandFUFSWInstPair(MBB, MBBI, NextMBBI);
  case RISCV::PseudoLGA:
    return expandLoadGlobalAddress(MBB, MBBI, NextMBBI);
  case RISCV::PseudoLA_TLS_IE:
    return expandLoadTLSIEAddress(MBB, MBBI, NextMBBI);
  case RISCV::PseudoLA_TLS_GD:
    return expandLoadTLSGDAddress(MBB, MBBI, NextMBBI);
  }
  return false;
}

bool RISCVPreRAExpandPseudo::expandAuipcInstPair(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI, unsigned FlagsHi,
    unsigned SecondOpcode) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();

  Register DestReg = MI.getOperand(0).getReg();
  Register ScratchReg =
      MF->getRegInfo().createVirtualRegister(&RISCV::GPRRegClass);

  MachineOperand &Symbol = MI.getOperand(1);
  Symbol.setTargetFlags(FlagsHi);
  MCSymbol *AUIPCSymbol = MF->getContext().createNamedTempSymbol("pcrel_hi");

  MachineInstr *MIAUIPC =
      BuildMI(MBB, MBBI, DL, TII->get(RISCV::AUIPC), ScratchReg).add(Symbol);
  MIAUIPC->setPreInstrSymbol(*MF, AUIPCSymbol);

  MachineInstr *SecondMI =
      BuildMI(MBB, MBBI, DL, TII->get(SecondOpcode), DestReg)
          .addReg(ScratchReg)
          .addSym(AUIPCSymbol, RISCVII::MO_PCREL_LO);

  if (MI.hasOneMemOperand())
    SecondMI->addMemOperand(*MF, *MI.memoperands_begin());

  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFULDInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LD), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LD), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

    //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULD "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> ld "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "ld " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFULWUInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LWU), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LWU), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

    //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULWU "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> lwu "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "lwu " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFULHInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LH), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LH), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULH "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> lhu "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "lhu " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFULHUInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LHU), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LHU), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULHU "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> lhu "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "lhu " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");
    
  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFULBInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LB), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LB), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULB "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> lb "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "lb " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFULBUInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LBU), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LBU), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULBU "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> lbu "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "lbu " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFULWInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LW), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::LW), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFULW "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> lw "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "lw " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUFLWInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FLW), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FLW), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  //dump first and second load
LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFUFLW "
                  << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) 
                  << " (" << printReg(SrcReg, TRI) << "), "
                  << "Offsets: " << Offset1 << ", " << Offset2 << " -> flw "
                  << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                  << "flw " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUFLDInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register DestReg = MI.getOperand(0).getReg();
  Register DestReg1 = MI.getOperand(1).getReg();
  Register SrcReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FLD), DestReg)
    .addReg(SrcReg)
    .addImm(Offset1);

  // Second load
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FLD), DestReg1)
    .addReg(SrcReg)
    .addImm(Offset2);

  LLVM_DEBUG(dbgs() << "Expanded fused load pseudo: PseudoFUFLD "
                    << printReg(DestReg, TRI) << ", " << printReg(DestReg1, TRI) << " (" << SrcReg << "), "
                    << printReg(Offset1, TRI) << " (" << Offset2 << ", TRI) -> fld "
                    << printReg(DestReg, TRI) << ", " << Offset1 << "(" << printReg(SrcReg, TRI) << "), "
                    << "fld " << printReg(DestReg1, TRI) << ", " << Offset2 << "(" << printReg(SrcReg, TRI) << ")\n");
  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUFSWInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register SrcReg1 = MI.getOperand(0).getReg();
  Register SrcReg2 = MI.getOperand(1).getReg();
  Register BaseReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FSW))
    .addReg(SrcReg1)
    .addReg(BaseReg)
    .addImm(Offset1);

  // Second store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FSW))
    .addReg(SrcReg2)
    .addReg(BaseReg)
    .addImm(Offset2);

    LLVM_DEBUG(dbgs() << "Expanded fused store pseudo: PseudoFUFSW "
                  << printReg(SrcReg1, TRI) << " (" << Offset1 << "), "
                  << printReg(SrcReg2, TRI) << " (" << Offset2 << ") -> fsw "
                  << printReg(SrcReg1, TRI) << ", " << Offset1 << "(" << printReg(BaseReg, TRI) << "), "
                  << "fsw " << printReg(SrcReg2, TRI) << ", " << Offset2 << "(" << printReg(BaseReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUFSDInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register SrcReg1 = MI.getOperand(0).getReg();
  Register SrcReg2 = MI.getOperand(1).getReg();
  Register BaseReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FSD))
    .addReg(SrcReg1)
    .addReg(BaseReg)
    .addImm(Offset1);

  // Second store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::FSD))
    .addReg(SrcReg2)
    .addReg(BaseReg)
    .addImm(Offset2);
  LLVM_DEBUG(dbgs() << "Expanded fused store pseudo: PseudoFUFSD "
                  << printReg(SrcReg1, TRI) << " (" << Offset1 << "), "
                  << printReg(SrcReg2, TRI) << " (" << Offset2 << ") -> fsd "
                  << printReg(SrcReg1, TRI) << ", " << Offset1 << "(" << printReg(BaseReg, TRI) << "), "
                  << "fsd " << printReg(SrcReg2, TRI) << ", " << Offset2 << "(" << printReg(BaseReg, TRI) << ")\n");
  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUSDInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register SrcReg1 = MI.getOperand(0).getReg();
  Register SrcReg2 = MI.getOperand(1).getReg();
  Register BaseReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();


MachineInstr *Store1 =
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::SD))
        .addReg(SrcReg1)
        .addReg(BaseReg)
        .addImm(Offset1)
        .getInstr();

MachineInstr *Store2 =
    BuildMI(MBB, MBBI, DL, TII->get(RISCV::SD))
        .addReg(SrcReg2)
        .addReg(BaseReg)
        .addImm(Offset2)
        .getInstr();

LLVM_DEBUG(dbgs() << "Expanded fused store pseudo: PseudoFUSD "
                  << printReg(SrcReg1, TRI) << " (" << Offset1 << "), "
                  << printReg(SrcReg2, TRI) << " (" << Offset2 << ") -> fsd "
                  << printReg(SrcReg1, TRI) << ", " << Offset1 << "(" << printReg(BaseReg, TRI) << "), "
                  << "fsd " << printReg(SrcReg2, TRI) << ", " << Offset2 << "(" << printReg(BaseReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUSWInstPair(
  MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
  MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register SrcReg1 = MI.getOperand(0).getReg();
  Register SrcReg2 = MI.getOperand(1).getReg();
  Register BaseReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SW))
    .addReg(SrcReg1)
    .addReg(BaseReg)
    .addImm(Offset1);

  // Second store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SW))
    .addReg(SrcReg2)
    .addReg(BaseReg)
    .addImm(Offset2);

  LLVM_DEBUG(dbgs() << "Expanded fused store pseudo: PseudoFUSH "
                  << printReg(SrcReg1, TRI) << " (" << Offset1 << "), "
                  << printReg(SrcReg2, TRI) << " (" << Offset2 << ") -> fsw "
                  << printReg(SrcReg1, TRI) << ", " << Offset1 << "(" << printReg(BaseReg, TRI) << "), "
                  << "fsw " << printReg(SrcReg2, TRI) << ", " << Offset2 << "(" << printReg(BaseReg, TRI) << ")\n");

  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandFUSHInstPair(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register SrcReg1 = MI.getOperand(0).getReg();
  Register SrcReg2 = MI.getOperand(1).getReg();
  Register BaseReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SH))
      .addReg(SrcReg1)
      .addReg(BaseReg)
      .addImm(Offset1);

  // Second store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SH))
      .addReg(SrcReg2)
      .addReg(BaseReg)
      .addImm(Offset2);
  LLVM_DEBUG(dbgs() << "Expanded fused store pseudo: PseudoFUSH "
                    << printReg(SrcReg1, TRI) << " (" << Offset1 << "), "
                    << printReg(SrcReg2, TRI) << " (" << Offset2 << ") -> fsh "
                    << printReg(SrcReg1, TRI) << ", " << Offset1 << "(" << printReg(BaseReg, TRI) << "), "
                    << "fsh " << printReg(SrcReg2, TRI) << ", " << Offset2 << "(" << printReg(BaseReg, TRI) << ")\n");
  MI.eraseFromParent();
  return true;
}
bool RISCVPreRAExpandPseudo::expandFUSBInstPair(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI) {
  MachineFunction *MF = MBB.getParent();
  MachineInstr &MI = *MBBI;
  DebugLoc DL = MI.getDebugLoc();
  const TargetRegisterInfo *TRI = MF->getSubtarget().getRegisterInfo();
  Register SrcReg1 = MI.getOperand(0).getReg();
  Register SrcReg2 = MI.getOperand(1).getReg();
  Register BaseReg = MI.getOperand(2).getReg();
  int64_t Offset1 = MI.getOperand(3).getImm();
  int64_t Offset2 = MI.getOperand(4).getImm();

  // First store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SB))
      .addReg(SrcReg1)
      .addReg(BaseReg)
      .addImm(Offset1);

  // Second store
  BuildMI(MBB, MBBI, DL, TII->get(RISCV::SB))
      .addReg(SrcReg2)
      .addReg(BaseReg)
      .addImm(Offset2);
  LLVM_DEBUG(dbgs() << "Expanded fused store pseudo: PseudoFUSB "
                    << printReg(SrcReg1, TRI) << " (" << Offset1 << "), "
                    << printReg(SrcReg2, TRI) << " (" << Offset2 << ") -> fsb "
                    << printReg(SrcReg1, TRI) << ", " << Offset1 << "(" << printReg(BaseReg, TRI) << "), "
                    << "fsb " << printReg(SrcReg2, TRI) << ", " << Offset2 << "(" << printReg(BaseReg, TRI) << ")\n");
  MI.eraseFromParent();
  return true;
}

bool RISCVPreRAExpandPseudo::expandLoadLocalAddress(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI) {
  return expandAuipcInstPair(MBB, MBBI, NextMBBI, RISCVII::MO_PCREL_HI,
                             RISCV::ADDI);
}

bool RISCVPreRAExpandPseudo::expandLoadGlobalAddress(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI) {
  unsigned SecondOpcode = STI->is64Bit() ? RISCV::LD : RISCV::LW;
  return expandAuipcInstPair(MBB, MBBI, NextMBBI, RISCVII::MO_GOT_HI,
                             SecondOpcode);
}

bool RISCVPreRAExpandPseudo::expandLoadTLSIEAddress(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI) {
  unsigned SecondOpcode = STI->is64Bit() ? RISCV::LD : RISCV::LW;
  return expandAuipcInstPair(MBB, MBBI, NextMBBI, RISCVII::MO_TLS_GOT_HI,
                             SecondOpcode);
}

bool RISCVPreRAExpandPseudo::expandLoadTLSGDAddress(
    MachineBasicBlock &MBB, MachineBasicBlock::iterator MBBI,
    MachineBasicBlock::iterator &NextMBBI) {
  return expandAuipcInstPair(MBB, MBBI, NextMBBI, RISCVII::MO_TLS_GD_HI,
                             RISCV::ADDI);
}

} // end of anonymous namespace

INITIALIZE_PASS(RISCVExpandPseudo, "riscv-expand-pseudo",
                RISCV_EXPAND_PSEUDO_NAME, false, false)

INITIALIZE_PASS(RISCVPreRAExpandPseudo, "riscv-prera-expand-pseudo",
                RISCV_PRERA_EXPAND_PSEUDO_NAME, false, false)

namespace llvm {

FunctionPass *createRISCVExpandPseudoPass() { return new RISCVExpandPseudo(); }
FunctionPass *createRISCVPreRAExpandPseudoPass() { return new RISCVPreRAExpandPseudo(); }

} // end of namespace llvm
