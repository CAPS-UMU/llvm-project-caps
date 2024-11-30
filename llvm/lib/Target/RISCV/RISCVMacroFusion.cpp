//===- RISCVMacroFusion.cpp - RISC-V Macro Fusion -------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file This file contains the RISC-V implementation of the DAG scheduling
/// mutation to pair instructions back to back.
//
//===----------------------------------------------------------------------===//
//
#include "RISCVMacroFusion.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "RISCVSubtarget.h"
#include "llvm/CodeGen/MacroFusion.h"
#include "llvm/CodeGen/TargetInstrInfo.h"

#define DEBUG_TYPE "riscv-macro-fusion"
using namespace llvm;

static bool checkRegisters(Register FirstDest, const MachineInstr &SecondMI) {
  if (!SecondMI.getOperand(1).isReg())
    return false;
  LLVM_DEBUG(dbgs() << "  Bind Norm ";);
  if (SecondMI.getOperand(1).getReg() != FirstDest)
    return false;

  // If the input is virtual make sure this is the only user.
  if (FirstDest.isVirtual()) {
    auto &MRI = SecondMI.getMF()->getRegInfo();
    return MRI.hasOneNonDBGUse(FirstDest);
  }

  return SecondMI.getOperand(0).getReg() == FirstDest;
}

static bool checkRegistersLoad(Register FirstDest, const MachineInstr &SecondMI) {
  if (!SecondMI.getOperand(0).isReg())
    return false;

  if (SecondMI.getOperand(1).getReg() != FirstDest)
    return false;

  if (!SecondMI.getOperand(2).isImm())
    return false;

  // if (!(SecondMI.getOperand(2).getImm() > -10000) && !(SecondMI.getOperand(2).getImm() < 10000))
  //   return false;

  // If the input is virtual make sure this is the only user.
  if (FirstDest.isVirtual()) {
    auto &MRI = SecondMI.getMF()->getRegInfo();
    return MRI.hasOneNonDBGUse(FirstDest);
  }

  LLVM_DEBUG(dbgs() << "  Bind Load"; SecondMI;
            dbgs() << " - "; FirstDest; dbgs() << '\n';);

  return SecondMI.getOperand(1).getReg() == FirstDest; //loads which access incremental address
}

static bool checkLoadRegisters(Register FirstDest, const MachineInstr &SecondMI) {
  if (!SecondMI.getOperand(1).isReg())
    return false;

  if (SecondMI.getOperand(2).isReg())
    return false;

  return SecondMI.getOperand(1).getReg() == FirstDest; //loads which access incremental address
}

static bool isFusedLB(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LB)
    return false;
  
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  if(FirstMI->getOpcode() !=RISCV::LB)
    return false;
  
  return checkRegistersLoad(FirstMI->getOperand(0).getReg(), SecondMI);
}

static bool isFusedLBU(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LBU)
    return false;
  
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  if(FirstMI->getOpcode() !=RISCV::LBU)
    return false;
  
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedLH(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LH)
    return false;
  
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  LLVM_DEBUG(dbgs() << "  Bind lh"; FirstMI;
            dbgs() << " - "; dbgs() << '\n';);

  if(FirstMI->getOpcode() !=RISCV::LH)
    return false;
  
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedLHU(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LHU)
    return false;
  
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  LLVM_DEBUG(dbgs() << "  Bind lhu";
            dbgs() << " - "; dbgs() << '\n';);

  if(FirstMI->getOpcode() !=RISCV::LHU)
    return false;
  
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedLW(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LW)
    return false;
  
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  LLVM_DEBUG(dbgs() << "  Bind lw";
            dbgs() << " - "; dbgs() << '\n';);

  if(FirstMI->getOpcode() !=RISCV::LW)
    return false;
  
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedLWU(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LWU)
    return false;
  
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;
  LLVM_DEBUG(dbgs() << "  Bind lwu";
            dbgs() << " - "; dbgs() << '\n';);

  if(FirstMI->getOpcode() !=RISCV::LWU)
    return false;
  
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedLD(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::LD)
    return false;
  LLVM_DEBUG(dbgs() << "  Bind ld";
            dbgs() << " SecondMI: "; SecondMI.print(dbgs()); dbgs() << '\n';);
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;
  LLVM_DEBUG(dbgs() << "  Bind ld1";
            dbgs() << " FirstMI: "; FirstMI->print(dbgs()); dbgs() << '\n';);
  if(FirstMI->getOpcode() != RISCV::LD){
    LLVM_DEBUG(dbgs() << "  false";
     dbgs() << " FirstMI: "; FirstMI->print(dbgs()); dbgs() << '\n';);
    return false;
  }

  LLVM_DEBUG(dbgs() << "  Bind ld2"; FirstMI->getOpcode() !=RISCV::LD;
            dbgs() << " - "; dbgs() << '\n';);
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedFLD(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::FLD)
    return false;
  LLVM_DEBUG(dbgs() << "  Bind fld";
            dbgs() << " - "; dbgs() << '\n';);
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;
  LLVM_DEBUG(dbgs() << "  Bind fld2";
            dbgs() << " - "; dbgs() << '\n';);
  if(FirstMI->getOpcode() != RISCV::FLD)
    LLVM_DEBUG(dbgs() << "  false";);
    return false;

  LLVM_DEBUG(dbgs() << "  Bind fld3";
            dbgs() << " - "; dbgs() << '\n';);
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

static bool isFusedFLW(const MachineInstr *FirstMI, const MachineInstr &SecondMI){
  if(SecondMI.getOpcode() != RISCV::FLW)
    return false;
  LLVM_DEBUG(dbgs() << "  Bind flw";
            dbgs() << " SecondMI: "; SecondMI.print(dbgs()); dbgs() << '\n';);
   // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!SecondMI.getOperand(2).isImm())
    return false;

  LLVM_DEBUG(dbgs() << "  Bind flw second MI use imm \n";);

  if (!FirstMI)
    return true;

  LLVM_DEBUG(dbgs() << "  Bind flw1";
            dbgs() << " FirstMI: "; FirstMI->print(dbgs()); dbgs() << '\n';);

  if(FirstMI->getOpcode() != RISCV::FLW) {
    LLVM_DEBUG(dbgs() << "  false \n";);
    return false;
  }

  LLVM_DEBUG(dbgs() << "  Bind flw3";
            dbgs() << " - "; dbgs() << '\n';);
  return checkRegistersLoad(FirstMI->getOperand(1).getReg(), SecondMI);
}

// Fuse load with add:
// add rd, rs1, rs2
// ld rd, 0(rd)
static bool isLDADD(const MachineInstr *FirstMI, const MachineInstr &SecondMI) {
  if (SecondMI.getOpcode() != RISCV::LD)
    return false;

  if (!SecondMI.getOperand(2).isImm())
    return false;

  if (SecondMI.getOperand(2).getImm() != 0)
    return false;

  // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  if (FirstMI->getOpcode() != RISCV::ADD)
    return false;

  return checkRegisters(FirstMI->getOperand(0).getReg(), SecondMI);
}

// Fuse two FLW instructions with the same base register:
// flw rd1, offset1(rs1)
// flw rd2, offset2(rs1)
static bool isFusedFLWPair(const MachineInstr *FirstMI, const MachineInstr &SecondMI) {
  if (SecondMI.getOpcode() != RISCV::FLW)
    return false;

  LLVM_DEBUG(dbgs() << "  flw";
            dbgs() << " SecondMI: "; SecondMI.print(dbgs()); dbgs() << '\n';);
   // Given SecondMI, when FirstMI is unspecified, we must return

  if (!SecondMI.getOperand(2).isImm())
    return false;
   // Given SecondMI, when FirstMI is unspecified, we must return

  // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  LLVM_DEBUG(dbgs() << "  flw";
            dbgs() << " FirstMI: "; FirstMI->print(dbgs()); dbgs() << '\n';);

  // if (FirstMI->getOpcode() != RISCV::FLW)
  //   return false;

  // Check if both instructions use the same base register
  // if (FirstMI->getOperand(1).getReg() != SecondMI.getOperand(1).getReg())
  //   return false;

  LLVM_DEBUG(dbgs() << "  Bind flw pair";
             dbgs() << " FirstMI: "; FirstMI->print(dbgs()); dbgs() << " - ";
             dbgs() << " SecondMI: "; SecondMI.print(dbgs()); dbgs() << '\n';);

  return true;
}

// Fuse these patterns:
//
// slli rd, rs1, 32
// srli rd, rd, x
// where 0 <= x <= 32
//
// and
//
// slli rd, rs1, 48
// srli rd, rd, x
static bool isShiftedZExt(const MachineInstr *FirstMI,
                          const MachineInstr &SecondMI) {
  if (SecondMI.getOpcode() != RISCV::SRLI)
    return false;

  if (!SecondMI.getOperand(2).isImm())
    return false;

  unsigned SRLIImm = SecondMI.getOperand(2).getImm();
  bool IsShiftBy48 = SRLIImm == 48;
  if (SRLIImm > 32 && !IsShiftBy48)
    return false;

  // Given SecondMI, when FirstMI is unspecified, we must return
  // if SecondMI may be part of a fused pair at all.
  if (!FirstMI)
    return true;

  if (FirstMI->getOpcode() != RISCV::SLLI)
    return false;

  unsigned SLLIImm = FirstMI->getOperand(2).getImm();
  if (IsShiftBy48 ? (SLLIImm != 48) : (SLLIImm != 32))
    return false;

  return checkRegisters(FirstMI->getOperand(0).getReg(), SecondMI);
}

// Fuse AUIPC followed by ADDI
// auipc rd, imm20
// addi rd, rd, imm12
static bool isAUIPCADDI(const MachineInstr *FirstMI,
                        const MachineInstr &SecondMI) {
  if (SecondMI.getOpcode() != RISCV::ADDI)
    return false;
  // Assume the 1st instr to be a wildcard if it is unspecified.
  if (!FirstMI)
    return true;

  if (FirstMI->getOpcode() != RISCV::AUIPC)
    return false;

  return checkRegisters(FirstMI->getOperand(0).getReg(), SecondMI);
}

// Fuse LUI followed by ADDI or ADDIW.
// rd = imm[31:0] which decomposes to
// lui rd, imm[31:12]
// addi(w) rd, rd, imm[11:0]
static bool isLUIADDI(const MachineInstr *FirstMI,
                      const MachineInstr &SecondMI) {
  if (SecondMI.getOpcode() != RISCV::ADDI &&
      SecondMI.getOpcode() != RISCV::ADDIW)
    return false;
  // Assume the 1st instr to be a wildcard if it is unspecified.
  if (!FirstMI)
    return true;

  if (FirstMI->getOpcode() != RISCV::LUI)
    return false;

  return checkRegisters(FirstMI->getOperand(0).getReg(), SecondMI);
}

static bool shouldScheduleAdjacent(const TargetInstrInfo &TII,
                                   const TargetSubtargetInfo &TSI,
                                   const MachineInstr *FirstMI,
                                   const MachineInstr &SecondMI) {
  const RISCVSubtarget &ST = static_cast<const RISCVSubtarget &>(TSI);

  if (ST.hasLUIADDIFusion() && isLUIADDI(FirstMI, SecondMI))
    return true;

  // if(ST.hasLoadFusion() && (isFusedLB(FirstMI, SecondMI)))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedLBU(FirstMI, SecondMI) ))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedLH(FirstMI, SecondMI)))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedLHU(FirstMI, SecondMI)))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedLW(FirstMI, SecondMI)))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedLWU(FirstMI, SecondMI)))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedLD(FirstMI, SecondMI)))
  //   return true;

  // if(ST.hasLoadFusion() && (isFusedFLD(FirstMI, SecondMI)))
  //   return true;

  if(ST.hasLoadFusion() && (isFusedFLW(FirstMI, SecondMI)))
    return true;

  if (ST.hasAUIPCADDIFusion() && isAUIPCADDI(FirstMI, SecondMI))
    return true;

  if (ST.hasShiftedZExtFusion() && isShiftedZExt(FirstMI, SecondMI))
    return true;

  if (ST.hasLDADDFusion() && isLDADD(FirstMI, SecondMI))
    return true;

  return false;
}

std::unique_ptr<ScheduleDAGMutation> llvm::createRISCVMacroFusionDAGMutation() {
  return createMacroFusionDAGMutation(shouldScheduleAdjacent);
}
