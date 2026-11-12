import FvModexp.Proofs.Amd64.Nat.NatAddBody
import FvModexp.Proofs.Amd64.Nat.NatAddSwap

/-!
# `nat.add` (go-bigmodexpfix nat.go:98), amd64: the summary (see the arm64 twin `FvModexp.Arm64.NatAdd`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatAdd

def names : List String := LibNatAdd.names

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = yp ∧ s.regs 10 = yl ∧ s.regs 11 = yc ∧ Pre R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => RegsOK s s' ∧ PostX 4440 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
  have hsp0 : 4440 ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simpa only [regSP] using this
  by_cases hyx : yl.toNat ≤ xl.toNat
  · obtain ⟨k, s', hst, hr, hq1, hq2⟩ := body impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc s hpc
      ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hyx, preS_mono (by omega) hpre⟩
    exact ⟨k, s', hst, hr, hq1, postX_mono (by omega) hsp0 hq2⟩
  · obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ : (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
        s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4440 < (s.regs 4).toNat ∧ 4440 ≤ (s.regs 4).toNat ∧
        (s.regs 4).toNat + 80 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat - 4440) (4440 + 80) true = true ∧
        (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
      obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
      simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
      exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩
    have hpre' := hpre
    obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, -, -, -, -, -, hx40, hy40, -⟩ := hpre'
    unfold Apart at hga
    janus64_run [BitVec.msb_eq_decide] until [segAddr Extracted.program fn + 0x2c7]
    janus64_step
    have hF1 : MemFrame s.mem (((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8
        zp.toNat).writeLE ((s.regs 4).toNat + 32) 8 xp.toNat).writeLE ((s.regs 4).toNat + 56) 8 yp.toNat).writeLE ((s.regs 4).toNat - 152) 8 6182956)
        (win s 4440 80) := by simp only [win]; janus_frame
    refine ReachesRet.call (body impl hap R hmk hmv b L zp zl zc yp yl yc xp xl xc) rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, preS_swap hpre rfl ?_ ?_ hF1 (by simp)⟩ ?_
    rotate_left
    all_goals try janus64_simp
    intro s2 hpc2 ⟨⟨hs2, h5', h14', hx15'⟩, hq⟩
    have hq' := hq
    obtain ⟨_, hmf, _⟩ := hq'
    have e152 : (s.regs 4 - 152#64).toNat = (s.regs 4).toNat - 152 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hzo : Outside zp.toNat (8 * zc.toNat) (win s 4440 80) := hpre.2.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at hzo
    have hrd : ∀ a, (s.regs 4).toNat - 8 ≤ a → a + 8 ≤ (s.regs 4).toNat + 8 → s2.mem.readLE a 8 =
        (((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8
        zp.toNat).writeLE ((s.regs 4).toNat + 32) 8 xp.toNat).writeLE ((s.regs 4).toNat + 56) 8 yp.toNat).writeLE ((s.regs 4).toNat - 152) 8 6182956).readLE a 8 := by
      intro a ha1 ha2
      refine hmf.readLE _ _ ?_
      simp only [win, Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152, outside_append,
        outside_cons, outside_nil, and_true]
      and_intros <;> first | exact hout.of_sub (by omega) (by omega) | omega
    have hr1 : s2.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [hrd _ (by omega) (by omega)]; janus64_simp
    have hr2 : s2.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [hrd _ (by omega) (by omega)]; janus64_simp
    janus64_run [hr1, hr2]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, postX_congr (postX_swap hpre (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) hF1 hq) ?_ ?_ ?_ rfl rfl ?dfc⟩
    case dfc =>
      have hd2 := hq.1.1.2.1
      rw [hd2]
    all_goals try janus64_simp
    all_goals try rw [h14']
    all_goals try rw [hx15']
    all_goals try janus64_simp

/-- **`nat.add`** (amd64, exact write set `PostX`): as `FvModexp.Arm64.NatAdd.ensX`. -/
theorem ensX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc) (PostX 4440 R b L zp zc xp xl yp yl) := by
  rw [show names = LibNatAdd.names from rfl, ← LibNatAdd.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      h_a7, h_a8, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- **`nat.add`** (amd64): as `FvModexp.Arm64.NatAdd.ens`. -/
theorem ensR (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc)
      (fun s s' => Post R b L zp zc xp xl yp yl s s' ∧
        (need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
        (mx xl yl < 2 ^ 39 → (s'.regs 1).toNat < 2 ^ 40)) :=
  Ensures.mono (ensX impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

/-- **`nat.add`** (amd64): as `FvModexp.Arm64.NatAdd.ens` (`ensR` without the extra conjuncts). -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc) (Post R b L zp zc xp xl yp yl) :=
  Ensures.mono (ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (A64.noExit_restrict64 hap names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.NatAdd
