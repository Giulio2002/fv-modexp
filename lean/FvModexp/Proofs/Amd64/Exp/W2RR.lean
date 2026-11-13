import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W2OneDefs

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `RR` gets exactly `numWords` words (nat.go:1402-1405), from the return of
`stk.nat(2n).div(stk, RR, zz, m)` (`divRet` = fn+0x61f) to the RR join `rrJ` (agent expmc s51; twin of `Arm64.W2RR`)

Code: `CMPQ SI, CX; JGE +0x74d` (`len RR ≥ n`: the remainder, register moves only) else `zz.make(n)` reuses `zz`
(`[0xa0] = cap zz ≥ n`, the `makeslice` branches +0x64d.. are refuted), `copy(zz, RR)` (memmove +0x720 unless the
pointers are equal, refuted by apartness), spills `0x100/0x128/0x248`, `RR = zz`; the words `zz[len RR : n]` are still
zero from `zz = 2^(128 n)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf)

/-- return of `nat.div` (RR) -/
abbrev divRet : Nat := 6212127

/-- the frame words `divRet → rrJ` writes (memmove window + return slot, spills) -/
@[reducible] def rw4 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4104, sp + 0x18), (sp + 0x100, sp + 0x108), (sp + 0x128, sp + 0x148), (sp + 0x248, sp + 0x368)]

/-- the facts at `rrJ` -/
@[reducible] def RRPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M M' : Memory)
    (rrp rrc : Nat) : Prop :=
  MemFrame M M' (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ LiveFrame M M' L [(zzp, zzp + 8 * n)] ∧
  R.inv b L g (view R.rt L M') ∧ M'.regions = M.regions ∧
  M'.readLE rrp (8 * n) = M.readLE rp (8 * rl) ∧
  ((rrp = rp ∧ rrc = rc ∧ rl = n) ∨ (rrp = zzp ∧ rrc = zzc ∧ rl < n))

set_option maxRecDepth 20000 in
/-- the post of the copy path, from the `memmove` post (pure) -/
theorem rrBpost {R : RtInv} {L : List (Nat × Nat)} {b g fs sp n rp rl rc zzp zzc : Nat} {M m1 : Memory}
    (he : Env R L g fs sp M) (hrln : rl < n) (hrw : Apart rp (8 * rl) (sp - 4296) (4296 + 0x2a8))
    (hzn : n ≤ zzc) (hzh : InRanges zzp (8 * zzc) L ∨ Outside zzp (8 * zzc) R.rt)
    (hzw : Apart zzp (8 * zzc) (sp - 4296) (4296 + 0x2a8)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (hF1 : MemFrame ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389) m1
      (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(zzp, zzp + 8 * rl)]))
    (hL1 : LiveFrame ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389) m1 L
      [(zzp, zzp + 8 * rl)])
    (hI1 : R.inv b L g (view R.rt L m1))
    (hC1 : Mem.Copied ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389) m1 zzp
      rp (8 * rl))
    (hrg1 : m1.regions =
      ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389).regions) :
    RRPost R b L g sp n rp rl rc zzp zzc M m1 zzp zzc := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, -⟩ := he0
  have u2 := hzw; have u1 := hrw
  unfold Apart at u1 u2
  have hw0 : MemFrame M ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389)
      (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) := by
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x100, sp + 0x108)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x128, sp + 0x148)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x248, sp + 0x368)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp - 4104, sp + 0x18)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  have hLw : LiveFrame M ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389) L
      [(zzp, zzp + 8 * n)] := by
    repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  refine ⟨?_, ?_, hI1, by simp only [Arm64.Memory.regions_writeLE] at hrg1 ⊢; exact hrg1, ?_, Or.inr ⟨rfl, rfl, hrln⟩⟩
  · refine hw0.trans hF1 (fun a k h => ⟨h, ?_⟩)
    simp only [rw4, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    refine ⟨⟨h.1.1, ?_⟩, ?_⟩ <;> omega
  · refine hLw.trans ⟨fun a k hin hout => hL1.readLE a k hin ?_⟩ (fun _ _ h => h)
    simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
  -- the value
  rw [show 8 * n = 8 * rl + 8 * (n - rl) by omega, Arm64.Memory.readLE_add, FvModexp.Expmc.readLE_of_copied hC1]
  have h2 : m1.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0 := by
    rw [← hzz0]
    have e : ((((M.writeLE (sp + 0x100) 8 zzc).writeLE (sp + 0x128) 8 n).writeLE (sp + 0x248) 8 zzp).writeLE (sp - 8) 8 6212389).readLE
        (zzp + 8 * rl) (8 * (n - rl)) = M.readLE (zzp + 8 * rl) (8 * (n - rl)) := by
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [← e]
    rcases hzh with h | h
    · exact hL1.readLE _ _ (h.sub (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)
    · exact hF1.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨⟨h.of_sub (by omega) (by omega), ?_⟩, ?_⟩ <;> omega)
  rw [h2]
  simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Nat.mul_zero, Nat.add_zero]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
/-- `divRet → rrJ`: `RR` = the remainder (`rl = n`) or `zz[0:n]` after `copy(zz, RR)` (`rl < n`) -/
theorem rrFix (impl : List Amd64.Segment) {R : RtInv}
    (hmv : MemmoveLive64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {ret : W64} {Q : State → Prop} (b : Nat) (L : List (Nat × Nat)) (g fs sp n rp rl rc zzp zzc : Nat) (M : Memory)
    (r5 : W64)
    (he : Env R L g fs sp M) (hn16 : n ≤ 2 ^ 16) (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4296) (4296 + 0x2a8))
    (hzn : n ≤ zzc) (hzzc : zzc < 2 ^ 40) (hzacc : M.accessible zzp (8 * zzc) true = true)
    (hz48 : zzp + 8 * zzc ≤ 2 ^ 48)
    (hzh : InRanges zzp (8 * zzc) L ∨ Outside zzp (8 * zzc) R.rt) (hzw : Apart zzp (8 * zzc) (sp - 4296) (4296 + 0x2a8))
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zzp, rp, 8 * rl])
    (hinv : R.inv b L g (view R.rt L M))
    (s3b0 : M.readLE (sp + 0x298) 8 = n) (sa0 : M.readLE (sp + 0xa0) 8 = zzc) (s188 : M.readLE (sp + 0x190) 8 = zzp)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 divRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h7 : S.regs 7 = BitVec.ofNat 64 rp) (h6 : S.regs 6 = BitVec.ofNat 64 rl) (h8 : S.regs 8 = BitVec.ofNat 64 rc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KR : ∀ (S' : State) (rrp rrc : Nat), S'.rip = BitVec.ofNat 64 rrJ → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 n → S'.regs 3 = BitVec.ofNat 64 rrp → S'.regs 1 = BitVec.ofNat 64 n →
      S'.regs 8 = BitVec.ofNat 64 rrc → S'.regs 2 = BitVec.ofNat 64 zzc → S'.regs 6 = BitVec.ofNat 64 zzp →
      S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      RRPost R b L g sp n rp rl rc zzp zzc M S'.mem rrp rrc →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have u1 := hrw; have u2 := hzw; have u3 := hzr
  unfold Apart at u1 u2 u3
  by_cases hA : rl = n
  · subst hA
    janus64_run [s3b0] until [6212454]
    refine KR _ rp rc rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfs ?_ rfl
      ⟨MemFrame.refl _ _, LiveFrame.refl _ _ _, hinv, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
    all_goals first | exact h5 | exact h8 | exact h14 | exact hx15 | exact hsp | exact BitVec.sub_add_cancel _ _ | rfl | skip
  · have hrl : rl < n := by omega
    have hne : zzp ≠ rp := by intro e; rw [e] at u3; omega
    have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
        ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
      intro r hr
      have := hLs r hr
      simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
      omega
    have hz8n : InRanges zzp (8 * rl) L ∨ Outside zzp (8 * rl) R.rt :=
      hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
    have hza : M.accessible zzp (8 * rl) true = true := Arm64.Memory.accessible_mono _ hzacc (Nat.le_refl _) (by omega)
    have hsel : (if (rl : Int) < (n : Int) then BitVec.ofNat 64 rl else BitVec.ofNat 64 n).toNat * 8 %
        18446744073709551616 = 8 * rl := by
      rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]; simp only [BitVec.toNat_ofNat]; omega
    janus64_run [s3b0, sa0, s188, hsel] until [6212454] calls [hmv L b]
    rename_i _ _ _ _ m1 _ _ hF1 hL1 hI1 hC1
    refine KR _ zzp zzc rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfs ?_ rfl
      (rrBpost he hrl hrw hzn hzh hzw hzz0 hF1 hL1 hI1 hC1 hrg1)
    all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact h5 | exact h8 | exact h14 | exact hx15 | exact hsp | exact BitVec.sub_add_cancel _ _ | rfl | skip

end FvModexp.Amd64.W2Pro
