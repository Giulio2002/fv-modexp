import FvModexp.Proofs.Amd64.Exp.SubMod2NGS4C

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: `J5G` → the `trunc` call (`+0x353`, return `+0x358`) → `s4tG`
(`z = z.trunc(z, n)`, `return z.add(z, natOne)`, nat.go:1754-1755) on the current array `(p, c)` (agent infra s49;
twin of Arm64/Exp/SubMod2NGS4Cb.lean)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s4cG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hadd : AddHypR impl R) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
    J5G impl R b L op zp zl zc yp yl yc n s := by
  intro S p c g L3 b3 hpre hpc hsp hab h0 h6 h1 h2 hfw hrt hlv hcur hc40 hp64 hWc hg hgz hlt hv
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -⟩ := id hpre
  have hent := hpre.ent
  simp only [K, A, regSP] at hout hb' ha hw
  have hs4 : 4576 ≤ (s.regs 4).toNat := by omega
  have hbb := bb_ok hpre hg fun h => (hgz h).2.2
  obtain ⟨hpw, hpg, hpf, -, -⟩ := curA_win hpre hcur
  have hW1 : 1 ≤ W n := by have := hpre.2.2.2.2.2.2.1; simp only [W]; omega
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have hzh : Held R L3 p (8 * c) := (hlv (by omega)).2.1
  have haccz : S.mem.accessible p (8 * c) true = true := (hlv (by omega)).2.2.1
  have hp48 : p + 8 * c ≤ 2 ^ 48 := (hlv (by omega)).2.2.2
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  have hstk : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hw
  have hzA : Outside p (8 * W n) (win s K A) := by
    simp only [win, K, A, W, outside_cons, outside_nil, and_true]; simp only [W] at hWc; omega
  unfold GoalG
  janus64_run [b136] until [6188320]
  have hF1 : MemFrame S.mem (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 136) 8 6216696) (win s K A) := by
    simp only [win, K, A]; janus_frame
  have hr1 : (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 136) 8 6216696).regions = S.mem.regions := by
    janus64_simp
  have hrt1 := rtG_stk hpre hrt hF1 hr1
  have hlv1 := natLive_store hlv ((s.regs 4).toNat - 136) 8 6216696
  have hxa : (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 136) 8 6216696).accessible p (8 * W n) false
      = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_sub _ haccz (Or.inr rfl) (Nat.le_refl _) (by simp only [W] at hWc ⊢; omega)
  have hfw1 := fwG_loC (lo := (s.regs 4).toNat - 4576)
    (M' := Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 136) 8 6216696) (by omega) hfw (by janus_frame)
  have hv1 := (natVal_frame hF1 hzA).trans hv
  refine truncCallW hap hns htr (zp := p) (zl := W n) (zc := c) (x := p) (xl := W n) (xc := c) (n := n)
    (ra := 6216696) (ra_of hap hnf 0x358 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp64 (by omega) hp64
    (by simp only [W]; omega) (by omega)
    (truncPreG_of hpre hbb hrt1 (by omega) rfl ?_ ?_ ?_ hkT haT hWc hc40 hlv1 (fun _ => ⟨hpw, hpg, hpf⟩)
      (by simp only [W]; omega) hxa (by simp only [W] at hWc ⊢; omega)
      (hzh.sub (Nat.le_refl _) (by simp only [W] at hWc ⊢; omega)) (by simp only [W] at hWc ⊢; omega)
      (by simp only [W]; omega) (Or.inl rfl))
    (Or.inr (Nat.le_refl _)) (Or.inl rfl)
    fun s' hpc' hsp' h14' hx' hreg' hpost => ?qK
  case qK =>
    refine s4tG impl hap hadd hpre hkT haT hcur hc40 hp64 hWc hg hgz _ hrt1 hlv1 hfw1 hlt hv1 _ rfl ?_ ?_ ?_ ?_ ?_
      s' hpc' hsp' h14' hx' hreg' hpost
    all_goals try janus64_simp
    · omega
    · exact hfs
  all_goals try janus64_simp
  · exact hent.2.2.2.1
  · omega
  · exact hfs

end FvModexp.Amd64.SubMod2N
