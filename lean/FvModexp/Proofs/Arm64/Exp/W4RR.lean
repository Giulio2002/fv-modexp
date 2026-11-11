import FvModexp.Proofs.Arm64.Exp.W4OneRet2
import FvModexp.Proofs.Arm64.Exp.W4ZcDefs

/-!
# window-4 prologue (arm64): `RR` gets exactly `numWords` words (nat.go:1398-1403), from the return of
`stk.nat(2n).div(stk, RR, zz, m)` (`divRet` = fn+0x41c) to `oneJ`

`len(RR) ≥ n` (then `= n`, `RR < m`): `RR` is the remainder. `len(RR) < n`: `zz = zz.make(n)` reuses `zz` (its
capacity is `≥ 2n + 1`, the `makeslice` branches are refuted), `copy(zz, RR)` (memmove), `RR = zz`; the words
`zz[len RR : n]` are still zero from `zz = 2^(128 n)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- return of `nat.div` (RR) -/
abbrev divRet : Nat := 1799564

/-- the frame words `divRet → oneJ` writes (memmove window, spills) -/
@[reducible] def rw4 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 168, sp + 176), (sp + 256, sp + 272), (sp + 304, sp + 312),
    (sp + 400, sp + 408), (sp + 832, sp + 840), (sp + 888, sp + 896)]

/-- the facts at `oneJ` -/
@[reducible] def RRPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M M' : Memory)
    (rrp rrc : Nat) : Prop :=
  MemFrame M M' (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ LiveFrame M M' L [(zzp, zzp + 8 * n)] ∧
  R.inv b L g (view R.rt L M') ∧ M'.regions = M.regions ∧
  M'.readLE (sp + 832) 8 = rrp ∧ M'.readLE (sp + 264) 8 = rrc ∧ M'.readLE (sp + 256) 8 = n ∧
  M'.readLE (sp + 400) 8 = zzp ∧ M'.readLE (sp + 168) 8 = zzc ∧ M'.readLE rrp (8 * n) = M.readLE rp (8 * rl) ∧
  ((rrp = rp ∧ rrc = rc ∧ rl = n) ∨ (rrp = zzp ∧ rrc = zzc ∧ rl < n))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem rrA (impl : List Segment) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (Q : Outcome → Prop) (R : RtInv) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn16 : n ≤ 2 ^ 16) (hrl : n ≤ rl) (hrl' : rl < 2 ^ 40) (hrc : rc < 2 ^ 40) (hrp : rp < 2 ^ 64)
    (hrln : rl ≤ n) (hra : Apart rp (8 * rl) (sp - 4288) (4288 + 1040)) (b : Nat) (hinv : R.inv b L g (view R.rt L M))
    (hzzp : zzp < 2 ^ 64) (hzzc : zzc < 2 ^ 40)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 rp) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KR : ∀ (S' : State) (M' : Memory) (rrp rrc : Nat), S'.pc = BitVec.ofNat 64 oneJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 n → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 →
      S'.mem = M' → RRPost R b L g sp n rp rl rc zzp zzc M M' rrp rrc →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have u := hra; unfold Apart at u
  janus_run [r1024, r168, r400] until [oneJ]
  refine KR _ _ rp rc ?_ ?_ ?_ ?_ ?_ ?_ rfl ⟨?_, ?_, ?_, by simp only [Memory.regions_writeLE], ?_, ?_, ?_, ?_, ?_, ?_,
    Or.inl ⟨rfl, rfl, by omega⟩⟩
  all_goals first | (janus_simp; done) | skip
  · repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 168, sp + 176)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 400, sp + 408)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 832, sp + 840)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 272)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  · repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  · repeat (refine inv_store_out ?_ (hwrt.of_sub (by omega) (by omega)))
    exact hinv
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.reducePow]
  all_goals first | omega | (rw [show rl = n by omega])


set_option maxRecDepth 20000 in
/-- the post of the copy path, from the `memmove` post (pure) -/
theorem rrBpost {R : RtInv} {L : List (Nat × Nat)} {b g sp n rp rl rc zzp zzc : Nat} {M m1 : Memory}
    (he : Env R L g sp M) (hrl0 : 0 < rl) (hrln : rl < n)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4288) (4288 + 1040))
    (hzn : n ≤ zzc) (hzh : InRanges zzp (8 * zzc) L ∨ Outside zzp (8 * zzc) R.rt)
    (hzw : Apart zzp (8 * zzc) (sp - 4288) (4288 + 1040)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (hzzp : zzp < 2 ^ 64) (hzzc : zzc < 2 ^ 40) (hn16 : n ≤ 2 ^ 16)
    (hF1 : MemFrame (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc) m1
      (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24)] ++ [(zzp, zzp + 8 * rl)]))
    (hL1 : LiveFrame (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc) m1 L
      [(zzp, zzp + 8 * rl)])
    (hI1 : R.inv b L g (view R.rt L m1))
    (hC1 : Mem.Copied (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc) m1 zzp rp
      (8 * rl))
    (hrg1 : m1.regions = (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc).regions) :
    RRPost R b L g sp n rp rl rc zzp zzc M
      (((((m1.writeLE (sp + 264) 8 zzc).writeLE (sp + 256) 8 n).writeLE (sp + 832) 8 zzp).writeLE (sp + 400) 8
        zzp).writeLE (sp + 168) 8 zzc) zzp zzc := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have u1 := hrw; have u2 := hzw
  unfold Apart at u1 u2
  have hw0 : MemFrame M (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc)
      (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) := by
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 304, sp + 312)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 888, sp + 896)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 272)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  refine ⟨?_, ?_, ?_, by simp only [Memory.regions_writeLE] at hrg1 ⊢; exact hrg1, ?_, ?_, ?_, ?_, ?_, ?_,
    Or.inr ⟨rfl, rfl, hrln⟩⟩
  · repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 168, sp + 176)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 400, sp + 408)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 832, sp + 840)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 272)) (by simp) (by simp only; omega) (by simp only; omega))
    refine hw0.trans hF1 (fun a k h => ⟨h, ?_⟩)
    simp only [rw4, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨⟨h.1.1, by omega, by omega⟩, by omega⟩
  · repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    have hLw : LiveFrame M (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc) L
        [(zzp, zzp + 8 * n)] := by
      repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
      exact LiveFrame.refl _ _ _
    refine hLw.trans ⟨fun a k hin hout => hL1.readLE a k hin ?_⟩ (fun _ _ h => h)
    simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
  · repeat (refine inv_store_out ?_ (hwrt.of_sub (by omega) (by omega)))
    exact hI1
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.reducePow]
  all_goals first | omega | skip
  -- the value
  rw [show 8 * n = 8 * rl + 8 * (n - rl) by omega, Memory.readLE_add, FvModexp.Expmc.readLE_of_copied hC1]
  have h2 : m1.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0 := by
    rw [← hzz0]
    have e : (((M.writeLE (sp + 304) 8 n).writeLE (sp + 888) 8 zzp).writeLE (sp + 264) 8 zzc).readLE (zzp + 8 * rl)
        (8 * (n - rl)) = M.readLE (zzp + 8 * rl) (8 * (n - rl)) := by
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [← e]
    rcases hzh with h | h
    · exact hL1.readLE _ _ (h.sub (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)
    · exact hF1.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨h.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  rw [h2]
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Nat.mul_zero, Nat.add_zero]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem rrB (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (Q : Outcome → Prop) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn16 : n ≤ 2 ^ 16) (hrl0 : 0 < rl) (hrln : rl < n) (hrc : rc < 2 ^ 40)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4288) (4288 + 1040))
    (hzn : n ≤ zzc) (hzzc : zzc < 2 ^ 40) (hzacc : M.accessible zzp (8 * zzc) true = true) (hz48 : zzp + 8 * zzc ≤ 2 ^ 48)
    (hzh : InRanges zzp (8 * zzc) L ∨ Outside zzp (8 * zzc) R.rt) (hzw : Apart zzp (8 * zzc) (sp - 4288) (4288 + 1040))
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zzp, rp, 8 * rl])
    (b : Nat) (hinv : R.inv b L g (view R.rt L M))
    (r1024 : M.readLE (sp + 1024) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 rp) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KR : ∀ (S' : State) (M' : Memory) (rrp rrc : Nat), S'.pc = BitVec.ofNat 64 oneJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 n → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 →
      S'.mem = M' → RRPost R b L g sp n rp rl rc zzp zzc M M' rrp rrc →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have u1 := hrw; have u2 := hzw; have u3 := hzr
  unfold Apart at u1 u2 u3
  have hne : zzp ≠ rp := by intro e; rw [e] at u3; omega
  have hz8n : InRanges zzp (8 * rl) L ∨ Outside zzp (8 * rl) R.rt :=
    hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hza : M.accessible zzp (8 * rl) true = true := Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
  have hsel : (if (rl : Int) < (n : Int) then BitVec.ofNat 64 rl else BitVec.ofNat 64 n) = BitVec.ofNat 64 rl := by
    rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
  janus_run [r1024, r168, r400, lsl3, e8n rl (by omega), hsel] until [oneJ] calls [hmv L b]
  rename_i _ _ _ _ _ m1 _ _ hF1 hL1 hI1 hC1
  refine KR _ _ zzp zzc ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (rrBpost he hrl0 hrln hrh hrw hzn hzh hzw hzz0 (by omega) hzzc hn16 hF1 hL1 hI1 hC1 (by janus_assumption))
  all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.W4Pro
