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

def SDT_StoreFusionPair : SDTypeProfile<0, 5, [SDTCisInt<0>,
                                         SDTCisSameAs<0, 1>,
                                         SDTCisPtrTy<2>,
                                         SDTCisVT<3, XLenVT>,
                                         SDTCisVT<4, XLenVT>]>;

def SDT_FStoreFusionPair : SDTypeProfile<0, 5, [
                                         SDTCisFP<0>,              // val1 is FP
                                         SDTCisSameAs<0, 1>,       // val1 == val2 (same FP type)
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
def fu_lwud : SDNode<"RISCVISD::FU_LWUD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_lbd : SDNode<"RISCVISD::FU_LBD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_lbud : SDNode<"RISCVISD::FU_LBUD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_lhd : SDNode<"RISCVISD::FU_LHD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;
def fu_lhud : SDNode<"RISCVISD::FU_LHUD", SDT_LoadFusionPair,
                    [SDNPHasChain, SDNPMayLoad, SDNPMemOperand]>;

def fu_fsw : SDNode<"RISCVISD::FU_FSW", SDT_FStoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_fsd : SDNode<"RISCVISD::FU_FSD", SDT_FStoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_swd : SDNode<"RISCVISD::FU_SWD", SDT_StoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_sdd : SDNode<"RISCVISD::FU_SDD", SDT_StoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_sdc : SDNode<"RISCVISD::FU_SDC", SDT_StoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_shd : SDNode<"RISCVISD::FU_SHD", SDT_StoreFusionPair,
                    [SDNPHasChain, SDNPMayStore, SDNPMemOperand]>;
def fu_sbd : SDNode<"RISCVISD::FU_SBD", SDT_StoreFusionPair,
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
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFLW : Pseudo<(outs FPR32:$rd, FPR32:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.flw", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteFLD32, WriteFLD32, ReadFMemBase]>{
                        let OutOperandList = (outs FPR32:$rd, FPR32:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                        let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

let Predicates = [IsRV64, HasStdExtD, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFLD : Pseudo<(outs FPR64:$rd, FPR64:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.fld", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteFLD64, WriteFLD64, ReadFMemBase]>{
                        let OutOperandList = (outs FPR64:$rd, FPR64:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                        let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULW : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lw", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDW, WriteLDW, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                         let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULWU : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lwud", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDW, WriteLDW, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                         let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

//same for lb
let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
     isPseudo = 1,isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULB : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lb", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDB, WriteLDB, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                         let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

//same for lbu
let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULBU : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lbud", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDB, WriteLDB, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                         let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}
//same for lh
let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0, 
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULH : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lh", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDH, WriteLDH, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                         let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}
//same for lhu
let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0, 
     isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULHU : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.lhud", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDH, WriteLDH, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                         let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
let hasSideEffects = 0, mayLoad = 1, mayStore = 0,  
    isPseudo = 1, isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFULD : Pseudo<(outs GPR:$rd, GPR:$rd2), (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.ld", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteLDD, WriteLDD, ReadMemBase]>{
                        let OutOperandList = (outs GPR:$rd, GPR:$rd2);
                        let InOperandList = (ins GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                        let Constraints = "@earlyclobber $rd,@earlyclobber $rd2";
                       }
}

//===----------------------------------------------------------------------===//
// Fusion specific pseudo-instructions for store operations
//===----------------------------------------------------------------------===//

let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1,  
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSW : Pseudo<(outs), (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.sw", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTW, WriteSTW, ReadStoreData, ReadMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1,  
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSD : Pseudo<(outs), (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.sd", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTD, WriteSTD, ReadStoreData, ReadMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}
let Predicates = [HasVendorFusionMemPair, IsRV64] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1,  
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSDC : Pseudo<
  (outs),
  (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
  [],
  "fu.sdc", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTD, WriteSTD, ReadStoreData, ReadMemBase]
> {
  let usesCustomInserter = 1;
  let OutOperandList = (outs);
  let InOperandList = (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
}
}
//same for sh
let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1, 
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSH : Pseudo<(outs), (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.sh", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTH, WriteSTH, ReadStoreData, ReadMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}
//same for sb
let Predicates = [HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1,  
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUSB : Pseudo<(outs), (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.sb", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteSTB, WriteSTB, ReadStoreData, ReadMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins GPR:$rd, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}

let Predicates = [IsRV64, HasStdExtF, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1,  
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFSW : Pseudo<(outs), (ins FPR32:$rd, FPR32:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.fsw", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteFST32, WriteFST32, ReadFStoreData, ReadFMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins FPR32:$rd, FPR32:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}

let Predicates = [IsRV64, HasStdExtD, HasVendorFusionMemPair] in {
let hasSideEffects = 0, mayLoad = 0, mayStore = 1,  
     isReMaterializable = 0, isAsmParserOnly = 0 in
def PseudoFUFSD : Pseudo<(outs), (ins FPR64:$rd, FPR64:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122), [],
                       "fu.fsd", "$rd, $rd2, (${rs1}), $imm12, $imm122">, Sched<[WriteFST64, WriteFST64, ReadFStoreData, ReadFMemBase]>{
                        let OutOperandList = (outs);
                        let InOperandList = (ins FPR64:$rd, FPR64:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122);
                       }
}
//===----------------------------------------------------------------------===//
let Predicates = [HasVendorFusionMemPair, IsRV64] in {
  def : Pat<(fu_lwd GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULW GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_ldd GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULD GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_lwud GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULWU GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_lbd GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULB GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_lbud GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULBU GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_lhd GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULH GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_lhud GPRMem:$rs1, simm12:$imm12, simm12:$imm122), (PseudoFULHU GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
}

let Predicates = [HasVendorFusionMemPair, IsRV64] in {
//   def : Pat<(fu_swd GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
//             (PseudoFUSW GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_swd (i32 GPR:$rd1), (i32 GPR:$rd2), GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSW GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_sdd (i64 GPR:$rd1), (i64 GPR:$rd2), GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSD GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_sdc (i64 GPR:$rd1), (i64 GPR:$rd2), GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSDC GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;            
  def : Pat<(fu_shd (i32 GPR:$rd1), (i32 GPR:$rd2), GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSH GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
  def : Pat<(fu_sbd (i32 GPR:$rd1), (i32 GPR:$rd2), GPRMem:$rs1, simm12:$imm12, simm12:$imm122),
            (PseudoFUSB GPR:$rd1, GPR:$rd2, GPRMem:$rs1, simm12:$imm12, simm12:$imm122)>;
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
//fld rd2 60(rd2)

//pseduofld rd2 rd1 rs1 10 60