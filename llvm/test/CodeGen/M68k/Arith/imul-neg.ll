; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=m68k-linux | FileCheck %s

define i8 @mul255_8(i8 %A) {
; CHECK-LABEL: mul255_8:
; CHECK:         .cfi_startproc
; CHECK-NEXT:  ; %bb.0:
; CHECK-NEXT:    move.b	(7,%sp), %d0
; CHECK-NEXT:    neg.b	%d0
; CHECK-NEXT:    rts
    %mul = mul i8 %A, 255
    ret i8 %mul
}

define i16 @mul65535_16(i16 %A) {
; CHECK-LABEL: mul65535_16:
; CHECK:         .cfi_startproc
; CHECK-NEXT:  ; %bb.0:
; CHECK-NEXT:    move.w	(6,%sp), %d0
; CHECK-NEXT:    neg.w	%d0
; CHECK-NEXT:    rts
    %mul = mul i16 %A, 65535
    ret i16 %mul
}

define i32 @mul4294967295_32(i32 %A) {
; CHECK-LABEL: mul4294967295_32:
; CHECK:         .cfi_startproc
; CHECK-NEXT:  ; %bb.0:
; CHECK-NEXT:    move.l	(4,%sp), %d0
; CHECK-NEXT:    neg.l	%d0
; CHECK-NEXT:    rts
    %mul = mul i32 %A, 4294967295
    ret i32 %mul
}

; NOTE: If returning a 64-bit integer, d0 will be the higher 32-bit!
define i64 @mul18446744073709551615_64(i64 %A) {
; CHECK-LABEL: mul18446744073709551615_64:
; CHECK:         .cfi_startproc
; CHECK-NEXT:  ; %bb.0:
; CHECK-NEXT:    move.l	(4,%sp), %d0
; CHECK-NEXT:    move.l	(8,%sp), %d1
; CHECK-NEXT:    neg.l	%d1
; CHECK-NEXT:    negx.l	%d0
; CHECK-NEXT:    rts
    %mul = mul i64 %A, 18446744073709551615
    ret i64 %mul
}