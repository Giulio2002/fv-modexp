import FvModexp.Proofs.Amd64.Exp.SlowJ
import FvModexp.Proofs.Amd64.Exp.SlowMod
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the four buffers `BB` and the upper loop's join states (agent expmc s79; twin of arm64
`SlowJ`'s `BB` + `SlowK`)

Every upper-loop segment module imports this one (ROW-TIME rule). The registers / slots (see `SlowDefs`):
* `KT1` at the test `t1` (`fnE + 0x28b`): `z = (AX, R10, R8)`, `zz = ([0x150], [0x70], [0x78])`,
  `r = ([0x160], [0x90], DX)`, `q = ([0x168], [0xa0], [0xa8])`, `j` CX, `v` R13, `w` R15 (= `[0x138]`),
  `BX = len x`, `SI = x.ptr`, `DI = stk`, `R9 = cap x`, `R11 = len y`, `R12 = y.ptr`;
* `KS1` at the `sqr` return `sq1R` (`fnE + 0x2e5`): the square `z` in `(AX, BX, CX)`, the old `z` (now `zz`) in
  `([0x188], [0x128], [0x130])`, `r = ([0x160], [0x90], [0x98])`, `q` as above, `j` `[0xb8]`, `v` `[0x88]`;
* `KD1` at the `len m` test `fnE + 0x39d`: `z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `v` in `DX`, slots as `KS1`;
* `KJ1` at the join `j1` (`fnE + 0x1f9`): `z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `q` in `(R15, R11, R9)`,
  `r = ([0x160], R12, R13)`, `v` in `DX`, `j` `[0xb8]`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the four buffers -/
structure BB (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat) : Prop where
  bz : LN R L st zp zc M L1 z zl zc' Zv
  bzz : DL R L st zp zc M L1 zz zzc
  lzz : zzl ≤ zzc
  br : DL R L st zp zc M L1 r rc
  lr : rl ≤ rc
  bq : DL R L st zp zc M L1 q qc
  lq : ql ≤ qc
  p1 : Pw z zc' zz zzc
  p2 : Pw z zc' r rc
  p3 : Pw z zc' q qc
  p4 : Pw zz zzc r rc
  p5 : Pw zz zzc q qc
  p6 : Pw r rc q qc

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- a destination's pointer and capacity fit a register -/
theorem DL.lt64 {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat}
    (h : DL R L st zp zc M L1 p c) : p < 2 ^ 64 ∧ c < 2 ^ 64 := by
  refine ⟨?_, by have := h.1; omega⟩
  rcases Nat.eq_zero_or_pos c with c0 | c0
  · rw [h.2.2.2.2 c0]; decide
  · have := (h.2.1 c0).2.2.2; omega

/-- `ResSep` from a callee's fresh-result clause -/
theorem rs_of {M M' : Memory} {st pd cd p c : Nat} (hc0 : stCap M' st = 0 → stW M' st = 0)
    (h : ¬ (p = pd ∧ c = cd) → 0 < c → 0 < stCap M' st → Apart p (8 * c) (stW M' st) (8 * stCap M' st)) :
    ¬ (p = pd ∧ c = cd) → ResSep M M' st p c := by
  intro hn hc _
  rcases Nat.eq_zero_or_pos (stCap M' st) with c0 | c0
  · rw [c0, hc0 c0]; unfold Apart; omega
  · exact h hn hc c0

/-- a callee's `NatOF` result re-pointed: an empty result is its destination's registers (`hE`), hence `nil` -/
theorem res_norm {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {pd cd need p' l' c' v : Nat} (hd : DL R L st zp zc M L1 pd cd)
    (hr : ExpHyp.NatOF R L1 L2 M' pd cd need p' l' c' v)
    (hE : c' = 0 → ¬ (p' = pd ∧ c' = cd) → BitVec.ofNat 64 p' = BitVec.ofNat 64 pd ∧ c' = cd) :
    ∃ p'', BitVec.ofNat 64 p'' = BitVec.ofNat 64 p' ∧ ExpHyp.NatOF R L1 L2 M' pd cd need p'' l' c' v ∧
      (c' = 0 → p'' = 0) ∧ (¬ (p'' = pd ∧ c' = cd) → p'' = p') ∧ (0 < c' → p'' = p') := by
  obtain ⟨hv, hn, hlc, hc40, hlv, hof⟩ := hr
  rcases Nat.eq_zero_or_pos c' with c0 | c0
  · subst c0
    have hl0 : l' = 0 := by omega
    subst hl0
    by_cases ho : p' = pd ∧ 0 = cd
    · obtain ⟨rfl, rfl⟩ := ho
      exact ⟨p', rfl, ⟨hv, hn, hlc, hc40, hlv, hof⟩, fun _ => hd.2.2.2.2 rfl, fun hn' => absurd ⟨rfl, rfl⟩ hn',
        fun h => absurd h (Nat.lt_irrefl 0)⟩
    · obtain ⟨e1, e2⟩ := hE rfl ho
      subst e2
      exact ⟨pd, e1.symm, ⟨by rw [← hv]; rfl, Or.inl rfl, Nat.le_refl _, hc40, by simp, Or.inl ⟨rfl, rfl⟩⟩,
        fun _ => hd.2.2.2.2 rfl, fun hn' => absurd ⟨rfl, rfl⟩ hn', fun h => absurd h (Nat.lt_irrefl 0)⟩
  · exact ⟨p', rfl, ⟨hv, hn, hlc, hc40, hlv, hof⟩, fun h => absurd h (by omega), fun _ => rfl, fun _ => rfl⟩


/-- at the upper test `t1` -/
structure KT1 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  w63 : w ≤ 63
  s138 : S.mem.readLE (sp + 0x138) 8 = w
  pc : S.rip = BitVec.ofNat 64 t1
  zlb : zl ≤ max xl ml
  jw : j ≤ w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e10 : S.regs 10 = BitVec.ofNat 64 zl
  e8 : S.regs 8 = BitVec.ofNat 64 zc'
  s150 : S.mem.readLE (sp + 0x150) 8 = zz
  s70 : S.mem.readLE (sp + 0x70) 8 = zzl
  s78 : S.mem.readLE (sp + 0x78) 8 = zzc
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  s90 : S.mem.readLE (sp + 0x90) 8 = rl
  e2 : S.regs 2 = BitVec.ofNat 64 rc
  s168 : S.mem.readLE (sp + 0x168) 8 = q
  sa0 : S.mem.readLE (sp + 0xa0) 8 = ql
  sa8 : S.mem.readLE (sp + 0xa8) 8 = qc
  e1 : S.regs 1 = BitVec.ofNat 64 j
  e13 : S.regs 13 = v
  e15 : S.regs 15 = BitVec.ofNat 64 w
  e3 : S.regs 3 = BitVec.ofNat 64 xl
  e6 : S.regs 6 = BitVec.ofNat 64 xp
  e7 : S.regs 7 = BitVec.ofNat 64 st
  e9 : S.regs 9 = BitVec.ofNat 64 xc
  e11 : S.regs 11 = BitVec.ofNat 64 yl
  e12 : S.regs 12 = BitVec.ofNat 64 yp

/-- at the `sqr` return `sq1R` (`z` = the square, `zz` = the old `z` in the slots) -/
structure KS1 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  w63 : w ≤ 63
  s138 : S.mem.readLE (sp + 0x138) 8 = w
  pc : S.rip = BitVec.ofNat 64 sq1R
  zlb : zl ≤ 2 * max xl ml
  jw : j < w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e3 : S.regs 3 = BitVec.ofNat 64 zl
  e1 : S.regs 1 = BitVec.ofNat 64 zc'
  s188 : S.mem.readLE (sp + 0x188) 8 = zz
  s128 : S.mem.readLE (sp + 0x128) 8 = zzl
  s130 : S.mem.readLE (sp + 0x130) 8 = zzc
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  s90 : S.mem.readLE (sp + 0x90) 8 = rl
  s98 : S.mem.readLE (sp + 0x98) 8 = rc
  s168 : S.mem.readLE (sp + 0x168) 8 = q
  sa0 : S.mem.readLE (sp + 0xa0) 8 = ql
  sa8 : S.mem.readLE (sp + 0xa8) 8 = qc
  sb8 : S.mem.readLE (sp + 0xb8) 8 = j
  s88 : S.mem.readLE (sp + 0x88) 8 = v.toNat

/-- at the `len m` test `fnE + 0x39d` (`z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `v` in `DX`) -/
structure KD1 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  w63 : w ≤ 63
  s138 : S.mem.readLE (sp + 0x138) 8 = w
  pc : S.rip = BitVec.ofNat 64 (fnE + 0x39d)
  zlb : zl ≤ 3 * max xl ml
  jw : j < w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e3 : S.regs 3 = BitVec.ofNat 64 zl
  e1 : S.regs 1 = BitVec.ofNat 64 zc'
  e8 : S.regs 8 = BitVec.ofNat 64 zz
  e6 : S.regs 6 = BitVec.ofNat 64 zzl
  e7 : S.regs 7 = BitVec.ofNat 64 zzc
  e2 : S.regs 2 = v
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  s90 : S.mem.readLE (sp + 0x90) 8 = rl
  s98 : S.mem.readLE (sp + 0x98) 8 = rc
  s168 : S.mem.readLE (sp + 0x168) 8 = q
  sa0 : S.mem.readLE (sp + 0xa0) 8 = ql
  sa8 : S.mem.readLE (sp + 0xa8) 8 = qc
  sb8 : S.mem.readLE (sp + 0xb8) 8 = j
  s88 : S.mem.readLE (sp + 0x88) 8 = v.toNat

/-- at the join `j1` (`z` in `(AX, BX, CX)`, `zz` in `(R8, SI, DI)`, `q` in `(R15, R11, R9)`, `r` in
`([0x160], R12, R13)`, the OLD `v` in `DX`) -/
structure KJ1 (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (j w : Nat) (v : BitVec 64) (z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc
  w63 : w ≤ 63
  s138 : S.mem.readLE (sp + 0x138) 8 = w
  pc : S.rip = BitVec.ofNat 64 j1
  zlb : zl ≤ max xl ml
  jw : j < w
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e3 : S.regs 3 = BitVec.ofNat 64 zl
  e1 : S.regs 1 = BitVec.ofNat 64 zc'
  e8 : S.regs 8 = BitVec.ofNat 64 zz
  e6 : S.regs 6 = BitVec.ofNat 64 zzl
  e7 : S.regs 7 = BitVec.ofNat 64 zzc
  e15 : S.regs 15 = BitVec.ofNat 64 q
  e11 : S.regs 11 = BitVec.ofNat 64 ql
  e9 : S.regs 9 = BitVec.ofNat 64 qc
  s160 : S.mem.readLE (sp + 0x160) 8 = rr
  e12 : S.regs 12 = BitVec.ofNat 64 rl
  e13 : S.regs 13 = BitVec.ofNat 64 rc
  e2 : S.regs 2 = v
  sb8 : S.mem.readLE (sp + 0xb8) 8 = j

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- `y`'s words at a context memory (port of arm64 `SlowKE.y_words`) -/
theorem y_words (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd (natVal s.mem yp yl) j := by
  intro j hj
  have hyO : OE R L sp K st s.mem yp (8 * yl) := hP.2.2.2.2.2.2.1
  have hb := oe_bytes hP hyO (fun hc => (hP.zF hc).2.2.2.2.2.2.2.1)
  rw [h.readB (hyO.1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
    fun i hi => by rw [Nat.add_assoc]; exact hb (8 * j + i) (by omega)]
  exact Expmc.readLE_wd s.mem yp j yl hj

end

end FvModexp.Amd64.ExpSlow
