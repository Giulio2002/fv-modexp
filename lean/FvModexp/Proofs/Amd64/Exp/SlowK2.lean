import FvModexp.Proofs.Amd64.Exp.SlowK

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the lower loop's join states (agent asm s74; twin of arm64 `SlowK2`, layout of expmc's
`SlowK`)

Every lower-loop segment module imports this one (ROW-TIME rule). `i` = the `y` word index (`[0xc0]`, `R11` at `t2`),
`j` = the bit index (`[0xb0]`); go-bigmodexpfix nat.go:766-783. Registers / slots (see `SlowDefs`):
* `KT2` at the test `t2` (`fnE + 0x589`): `z = (AX, R10, R8)`, `zz = ([0x150], [0x70], [0x78])`,
  `q = ([0x168], R13, R15)`, `r = ([0x160], CX, DX)`, `v` R9, `i` R11, `BX = len x`, `SI = x.ptr`, `DI = stk`;
* `KS2` at the `sqr` return `sq2R` (`fnE + 0x5fb`): the square `z` in `(AX, BX, CX)`, the old `z` (now `zz`) in
  `([0x170], [0xe0], [0xd8])`, `r = ([0x160], [0xf0], [0xe8])`, `q = ([0x168], [0x100], [0xf8])`, `v` `[0x88]`;
* `KD2` at the 2nd `len m` test `fnE + 0x6b3` (`MOVQ 0x1d8(SP), R10`): `z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`,
  `v` in `DX`, slots as `KS2`;
* `KE` at the exit `ex` (`fnE + 0x7c5`): `z = (AX, R10, R8)`;
* `KJ2` at the join `j2` (`fnE + 0x511`): `z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `q` in `(R15, R9, R11)`,
  `r = ([0x160], R12, R13)`, the OLD `v` in `DX`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- at the lower test `t2` -/
structure KT2 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (i j : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  iy : i + 2 ≤ yl
  sc0 : S.mem.readLE (sp + 0xc0) 8 = i
  sb0 : S.mem.readLE (sp + 0xb0) 8 = j
  pc : S.rip = BitVec.ofNat 64 t2
  zlb : zl ≤ max xl ml
  jw : j ≤ 64
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e10 : S.regs 10 = BitVec.ofNat 64 zl
  e8 : S.regs 8 = BitVec.ofNat 64 zc'
  s150 : S.mem.readLE (sp + 0x150) 8 = zz
  s70 : S.mem.readLE (sp + 0x70) 8 = zzl
  s78 : S.mem.readLE (sp + 0x78) 8 = zzc
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  e1 : S.regs 1 = BitVec.ofNat 64 rl
  e2 : S.regs 2 = BitVec.ofNat 64 rc
  s168 : S.mem.readLE (sp + 0x168) 8 = q
  e13 : S.regs 13 = BitVec.ofNat 64 ql
  e15 : S.regs 15 = BitVec.ofNat 64 qc
  e9 : S.regs 9 = v
  e11 : S.regs 11 = BitVec.ofNat 64 i
  e3 : S.regs 3 = BitVec.ofNat 64 xl
  e6 : S.regs 6 = BitVec.ofNat 64 xp
  e7 : S.regs 7 = BitVec.ofNat 64 st

/-- at the `sqr` return `sq2R` (`z` = the square, `zz` = the old `z` in the slots) -/
structure KS2 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (i j : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  iy : i + 2 ≤ yl
  sc0 : S.mem.readLE (sp + 0xc0) 8 = i
  sb0 : S.mem.readLE (sp + 0xb0) 8 = j
  pc : S.rip = BitVec.ofNat 64 sq2R
  zlb : zl ≤ 2 * max xl ml
  jw : j < 64
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e3 : S.regs 3 = BitVec.ofNat 64 zl
  e1 : S.regs 1 = BitVec.ofNat 64 zc'
  s170 : S.mem.readLE (sp + 0x170) 8 = zz
  se0 : S.mem.readLE (sp + 0xe0) 8 = zzl
  sd8 : S.mem.readLE (sp + 0xd8) 8 = zzc
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  sf0 : S.mem.readLE (sp + 0xf0) 8 = rl
  se8 : S.mem.readLE (sp + 0xe8) 8 = rc
  s168 : S.mem.readLE (sp + 0x168) 8 = q
  s100 : S.mem.readLE (sp + 0x100) 8 = ql
  sf8 : S.mem.readLE (sp + 0xf8) 8 = qc
  s88 : S.mem.readLE (sp + 0x88) 8 = v.toNat

/-- at the 2nd `len m` test `fnE + 0x6b3` (`z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `v` in `DX`) -/
structure KD2 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (i j : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  iy : i + 2 ≤ yl
  sc0 : S.mem.readLE (sp + 0xc0) 8 = i
  sb0 : S.mem.readLE (sp + 0xb0) 8 = j
  pc : S.rip = BitVec.ofNat 64 (fnE + 0x6b3)
  zlb : zl ≤ 3 * max xl ml
  jw : j < 64
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e3 : S.regs 3 = BitVec.ofNat 64 zl
  e1 : S.regs 1 = BitVec.ofNat 64 zc'
  e8 : S.regs 8 = BitVec.ofNat 64 zz
  e6 : S.regs 6 = BitVec.ofNat 64 zzl
  e7 : S.regs 7 = BitVec.ofNat 64 zzc
  e2 : S.regs 2 = v
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  sf0 : S.mem.readLE (sp + 0xf0) 8 = rl
  se8 : S.mem.readLE (sp + 0xe8) 8 = rc
  s168 : S.mem.readLE (sp + 0x168) 8 = q
  s100 : S.mem.readLE (sp + 0x100) 8 = ql
  sf8 : S.mem.readLE (sp + 0xf8) 8 = qc
  s88 : S.mem.readLE (sp + 0x88) 8 = v.toNat

/-- at the join `j2` (`z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `q` in `(R15, R9, R11)`, `r` in
`([0x160], R12, R13)`, the OLD `v` in `DX`) -/
structure KJ2 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (i j : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  iy : i + 2 ≤ yl
  sc0 : S.mem.readLE (sp + 0xc0) 8 = i
  sb0 : S.mem.readLE (sp + 0xb0) 8 = j
  pc : S.rip = BitVec.ofNat 64 j2
  zlb : zl ≤ max xl ml
  jw : j < 64
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e3 : S.regs 3 = BitVec.ofNat 64 zl
  e1 : S.regs 1 = BitVec.ofNat 64 zc'
  e8 : S.regs 8 = BitVec.ofNat 64 zz
  e6 : S.regs 6 = BitVec.ofNat 64 zzl
  e7 : S.regs 7 = BitVec.ofNat 64 zzc
  e15 : S.regs 15 = BitVec.ofNat 64 q
  e9 : S.regs 9 = BitVec.ofNat 64 ql
  e11 : S.regs 11 = BitVec.ofNat 64 qc
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  e12 : S.regs 12 = BitVec.ofNat 64 rl
  e13 : S.regs 13 = BitVec.ofNat 64 rc
  e2 : S.regs 2 = v

/-- at the exit `ex` (`fnE + 0x7c5`, `z.norm()`): `z` in `(AX, R10, R8)` -/
structure KE (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  pc : S.rip = BitVec.ofNat 64 ex
  zlb : zl ≤ max xl ml
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e10 : S.regs 10 = BitVec.ofNat 64 zl
  e8 : S.regs 8 = BitVec.ofNat 64 zc'

end FvModexp.Amd64.ExpSlow
