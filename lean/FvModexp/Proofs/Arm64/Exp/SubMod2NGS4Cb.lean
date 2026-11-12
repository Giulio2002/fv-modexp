import FvModexp.Proofs.Arm64.Exp.SubMod2NGS4C

set_option autoImplicit false

/-!
# `nat.subMod2N` (arm64), general form: `J5G` → the `trunc` call → `z = z.trunc(z, n)`, `return z.add(z, natOne)`
(nat.go:1754-1755) on the current array `(p, c)` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s4cG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hadd : AddHypR impl R) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
    J5G impl R b L op zp zl zc yp yl yc n s := by
  intro S p c g L3 b3 hpre hpc hsp h28 h18 h0 h1 h2 h9 hfw hrt hlv hcur hc40 hp64 hWc hg hgz hlt hv
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgrt, -, -⟩, -⟩ := id hpre
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hout hb' ha hw hg3 hga
  have hs4 : 4608 ≤ s.sp.toNat := by omega
  have hbb := bb_ok hpre hg fun h => (hgz h).2.2
  obtain ⟨hpw, hpg, -, -⟩ := curA_win hpre hcur
  have hW1 : 1 ≤ W n := by have := hpre.2.2.2.2.2.2.1; simp only [W]; omega
  have hWc' : (n + 63) / 64 ≤ c := hWc
  have hzh : Held R L3 p (8 * c) := (hlv (by omega)).2.1
  have haccz : S.mem.accessible p (8 * c) true = true := (hlv (by omega)).2.2.1
  have hp48 : p + 8 * c ≤ 2 ^ 48 := (hlv (by omega)).2.2.2
  rw [show (1805584 + 0x2ac : Nat) = 1806268 from rfl] at hpc
  unfold GoalG
  janus_run until [1786000]
  refine truncCall hap hns htr (zp := p) (zl := W n) (zc := c) (x := p) (xl := W n) (xc := c) (n := n)
    (ra_of hap hnf 176 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp64 (by omega) hp64
    (by simp only [W]; omega) (by omega) (by omega)
    (truncPreG_of hpre hbb hrt (by omega) ?_ ?_ ?_ hkT haT hWc hc40 hlv (fun _ => ⟨hpw, hpg⟩)
      (by simp only [W]; omega) ?_ (by simp only [W]; omega) (hzh.sub (Nat.le_refl _) (by simp only [W]; omega))
      (by omega) (by simp only [W]; omega) (Or.inl rfl))
    (Or.inr (by simp only [W]; omega)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hreg' hpost => ?qK
  case qK =>
    refine s4tG impl hap hadd hpre hkT haT hcur hc40 hp64 hWc hg hgz S.mem hrt hlv hfw hlt hv _ ?_ ?_ ?_ s' hpc' hsp'
      h28' ?_ hreg' hpost
    · rfl
    · janus_simp
    · janus_simp
    · rw [h18']; janus_simp
  all_goals try janus_simp
  exact Memory.accessible_sub _ haccz (Or.inr rfl) (Nat.le_refl _) (by simp only [W]; omega)

end FvModexp.Arm64.SubMod2N
