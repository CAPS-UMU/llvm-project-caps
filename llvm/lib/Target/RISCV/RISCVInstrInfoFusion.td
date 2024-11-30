//===-- RISCVInstrInfoFusion.td ----------------------------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file describes the psuedo instruction defined to aid Fusion.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Fusion specific DAG Nodes.
//===----------------------------------------------------------------------===//

def SDT_LoadFusionPair : SDTypeProfile<2, 3, [SDTCisSameAs<0, 1>,
                                        SDTCisSameAs<1, 3>,
                                        SDTCisPtrTy<2>,
                                        SDTCisVT<3, XLenVT>,
                                        SDTCisVT<4, XLenVT>]>;
def SDT_FLoadFusionPair : SDTypeProfile<2, 3, [
                                        SDTCisFP<0>,
                                        SDTCisFP<1>,
                                        SDTCisPtrTy<2>,
                                        SDTCisVT<3, XLenVT>,
                                        SDTCisVT<4, XLenVT>]>;

def SDT_StoreFusionPair : SDTypeProfile<0, 5, [SDTCisSameAs<0, 1>,
                                         SDTCisSameAs<1, 3>,
                                         SDTCisPtrTy<2>,
                                         SDTCisVT<3, XLenVT>,
                                         SDTCisVT<4, XLenVT>]>;

def SDT_FStoreFusionPair : SDTypeProfile<0, 5, [
                                         SDTCisFP<1>,
                                         SDTCisFP<0>,
                                         SDTCisPtrTy<2>,
                                         SDTCisVT<3, XLenVT>,
                                         SDTCisVT<4, XLenVT>]>;

def fu_lwd : SDNode<"RISCVISD::FU_LWD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_ldd : SDNode<"RISCVISD::FU_LDD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_flw : SDNode<"RISCVISD::FU_FLW", SDT_FLoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_fld : SDNode<"RISCVISD::FU_FLD", SDT_FLoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
                    
def fu_fsw : SDNode<"RISCVISD::FU_FSW", SDT_FStoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_fsd : SDNode<"RISCVISD::FU_FSD", SDT_FStoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_swd : SDNode<"RISCVISD::FU_SWD", SDT_StoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_sdd : SDNode<"RISCVISD::FU_SDD", SDT_StoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;

def simm12fu : RISCVSImmLeafOp<12> {
  let MCOperandPredicate = [{
    int64_t Imm;
    if (MCOp.evaluateAsConstantImm(Imm))
      return isInt<12>(Imm);
    return MCOp.isBareSymbolRef();
  }];
}

def loadf128 : PatFrag<(ops node:$ptr), (f128 (load node:$ptr))>;

let Predicates = [IsRV64, HasStdExtF, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFLW : Pseudo<(outs FPR32:$rd, FPR32:$rs2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.flw", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteFLD32, WriteFLD32, ReadFMemBase]>{
                        let OutOperandList = (outs FPR32:$rd, FPR32:$rs2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                        let Constraints = "@earlyclobber $rd,@earlyclobber $rs2";
                       }
}

let Predicates = [IsRV64, HasStdExtD, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFLD : Pseudo<(outs FPR64:$rd, FPR64:$rs2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.fld", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteFLD64, WriteFLD64, ReadFMemBase]>{
                        let OutOperandList = (outs FPR64:$rd, FPR64:$rs2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                        let Constraints = "@earlyclobber $rd,@earlyclobber $rs2";
                       }
}

let Predicates = [IsRV64, HasStdExtF, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFSW : Pseudo<(outs), (ins FPR32:$rd, FPR32:$rs2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.fsw", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteFST32, WriteFST32, ReadFStoreData, ReadFMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins FPR32:$rd, FPR32:$rs2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}

let Predicates = [IsRV64, HasStdExtD, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFSD : Pseudo<(outs), (ins FPR64:$rd, FPR64:$rs2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.fsd", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteFST64, WriteFST64, ReadFStoreData, ReadFMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins FPR64:$rd, FPR64:$rs2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}

let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULW : Pseudo<(outs GPR:$rd, GPR:$rs2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lw", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDW, WriteLDW, ReadMemBase]>;
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0, Size = 8, 
    isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULD : Pseudo<(outs GPR:$rd, GPR:$rs2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.ld", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDD, WriteLDD, ReadMemBase]>{
                        let Constraints = "@earlyclobber $rd,@earlyclobber $rs2";
                       }
}

let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSW : Pseudo<(outs), (ins GPR:$rd, GPR:$rs2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.sw", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTW, WriteSTW, ReadStoreData, ReadMemBase]>;
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1, Size = 8, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSD : Pseudo<(outs), (ins GPR:$rd, GPR:$rs2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.sd", "$rd, $rs2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTD, WriteSTD, ReadStoreData, ReadMemBase]>;
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
  def : Pat<(fu_lwd GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULW GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_ldd GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULD GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
  def : Pat<(fu_swd GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSW GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_sdd GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSD GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
}

let Predicates = [HasVendorFusionMemPair, HasStdExtD, IsRV64] in {
// def : Pat<(f128 (fu_fld GPRMem:$rs1, i64:$imm12, i64:$imm122)),
//           (PseudoFUFLD (!cast<SDNode>("load" # "i64") GPRMem:$rs1, i32:$imm12, i32:$imm122))>;
// def : Pat<(f128 (f64 (load (add GPRMem:$rs1, simm12:$imm12))),
//             (f64 (load (add GPRMem:$rs1, simm12:$imm122)))),
//          (f128 (PseudoFUFLD GPRMem:$rs1, simm12:$imm12, simm12:$imm122))>;
def : Pat<(fu_fld GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFUFLD GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
def : Pat<(fu_fsd FPR64:$rd1, FPR64:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
          (PseudoFUFSD FPR64:$rd1, FPR64:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
} //Predicates = [HasVendorFusionMemPair, HasStdExtD, IsRV64]

let Predicates = [HasVendorFusionMemPair, HasStdExtF, IsRV64] in {
 def : Pat<(fu_flw GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFUFLW GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
 def : Pat<(fu_fsw FPR32:$rd1, FPR32:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
           (PseudoFUFSW FPR32:$rd1, FPR32:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
} //Predicates = [HasVendorFusionMemPair, HasStdExtF]

// Define the pattern to match two floating-point loads with the same base register
//def : Pat<(f32 (load (add i32:$base, i32:$offset1))),
//           (f32 (load (add i32:$base, i32:$offset2)))>,
//          (PseudoFULW f32:$dest1, f32:$dest2, i32:$base, i32:$offset1, i32:$offset2)>;
// def : Pat<(f128 (fu_fld i64:$rs1, i64:$imm12, i64:$imm122))>, (PseudoFUFLD i64:$rs1, i64:$imm12, i64:$imm122)>;
// Define the pattern to match the pseudo-instruction


//fld rd1 10(rs1)
//fld rd2 60(rs2)

//pseduofld rd2 rd1 rs1 10 60