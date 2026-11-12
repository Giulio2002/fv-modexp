import FvModexp.Proofs.Arm64.Exp.SlowJF

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the upper loop's join states (agent expmc)

Every upper-loop segment module imports this one (ROW-TIME rule). The loop's registers at the test `T1`
(`fnE + 0x208`, `CMP R14, R13`): `z = (R0, R5, R2)`, `zz = (R24, R23, R22)`, `r = (R20, R15, R19)`,
`q = (R21, R17, R16)`, `j = R13`, `v = R9`, `w = R14` (slot 152), `st = R3`, `y = (R7, R8)`.
* `KT1`: at `T1`;
* `KS1`: at the `sqr` return `fnE + 0x254`: the square `z` in `X0..X2`, the old `z` (now `zz`) in slots
  336/120/128, `j` 208, `r` 352/168/176, `q` 360/184/192, `v` 160;
* `KD1`: at the `div` join `fnE + 0x2b4`: `z` in `X0..X2`, `zz` in `(X6, X4, X5)`, `v` in `X3`, slots as `KS1`.
The values of the buffers and the budget are tracked by the loop lemma (parameters `Zv`, `b1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- at the upper test `T1` -/
structure KT1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 (fnE + 0x208)
  jc : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc
  zl128 : zl ≤ 128
  jw : j ≤ w
  w63 : w ≤ 63
  s152 : S.mem.readLE (sp + 152) 8 = w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e5 : S.regs 5 = BitVec.ofNat 64 zl
  e2 : S.regs 2 = BitVec.ofNat 64 zc'
  e24 : S.regs 24 = BitVec.ofNat 64 zz
  e23 : S.regs 23 = BitVec.ofNat 64 zzl
  e22 : S.regs 22 = BitVec.ofNat 64 zzc
  e20 : S.regs 20 = BitVec.ofNat 64 r
  e15 : S.regs 15 = BitVec.ofNat 64 rl
  e19 : S.regs 19 = BitVec.ofNat 64 rc
  e21 : S.regs 21 = BitVec.ofNat 64 q
  e17 : S.regs 17 = BitVec.ofNat 64 ql
  e16 : S.regs 16 = BitVec.ofNat 64 qc
  e13 : S.regs 13 = BitVec.ofNat 64 j
  e9 : S.regs 9 = v
  e14 : S.regs 14 = BitVec.ofNat 64 w
  e3 : S.regs 3 = BitVec.ofNat 64 st
  e7 : S.regs 7 = BitVec.ofNat 64 yp
  e8 : S.regs 8 = BitVec.ofNat 64 yl

/-- at the `sqr` return `fnE + 0x254` (`z` = the square in `X0..X2`, `zz` = the old `z` in the slots) -/
structure KS1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 (fnE + 0x254)
  jc : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc
  zl256 : zl ≤ 256
  jw : j < w
  w63 : w ≤ 63
  s152 : S.mem.readLE (sp + 152) 8 = w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e1 : S.regs 1 = BitVec.ofNat 64 zl
  e2 : S.regs 2 = BitVec.ofNat 64 zc'
  s336 : S.mem.readLE (sp + 336) 8 = zz
  s120 : S.mem.readLE (sp + 120) 8 = zzl
  s128 : S.mem.readLE (sp + 128) 8 = zzc
  s352 : S.mem.readLE (sp + 352) 8 = r
  s168 : S.mem.readLE (sp + 168) 8 = rl
  s176 : S.mem.readLE (sp + 176) 8 = rc
  s360 : S.mem.readLE (sp + 360) 8 = q
  s184 : S.mem.readLE (sp + 184) 8 = ql
  s192 : S.mem.readLE (sp + 192) 8 = qc
  s208 : S.mem.readLE (sp + 208) 8 = j
  s160 : S.mem.readLE (sp + 160) 8 = v.toNat

/-- at the `div` join `fnE + 0x2b4` (`z` in `X0..X2`, `zz` in `(X6, X4, X5)`, `v` in `X3`) -/
structure KD1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 (fnE + 0x2b4)
  jc : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc
  zl384 : zl ≤ 384
  jw : j < w
  w63 : w ≤ 63
  s152 : S.mem.readLE (sp + 152) 8 = w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e1 : S.regs 1 = BitVec.ofNat 64 zl
  e2 : S.regs 2 = BitVec.ofNat 64 zc'
  e6 : S.regs 6 = BitVec.ofNat 64 zz
  e4 : S.regs 4 = BitVec.ofNat 64 zzl
  e5 : S.regs 5 = BitVec.ofNat 64 zzc
  e3 : S.regs 3 = v
  s352 : S.mem.readLE (sp + 352) 8 = r
  s168 : S.mem.readLE (sp + 168) 8 = rl
  s176 : S.mem.readLE (sp + 176) 8 = rc
  s360 : S.mem.readLE (sp + 360) 8 = q
  s184 : S.mem.readLE (sp + 184) 8 = ql
  s192 : S.mem.readLE (sp + 192) 8 = qc
  s208 : S.mem.readLE (sp + 208) 8 = j
  s160 : S.mem.readLE (sp + 160) 8 = v.toNat

end FvModexp.Arm64.ExpSlow
