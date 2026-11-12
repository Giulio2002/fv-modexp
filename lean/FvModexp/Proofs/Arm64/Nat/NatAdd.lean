import FvModexp.Proofs.Arm64.Nat.NatAddBody
import FvModexp.Proofs.Arm64.Nat.NatAddSwap

/-!
# `nat.add` (go-bigmodexpfix nat.go:98), arm64: the summary

`full`: the `Summary` at the entry for both orders of the operands (`len y ≤ len x`: `body`; `len x < len y`: the swap
and the self-call `z.add(y, x)`, served by `body`, then the epilogue). `ens`: the `Ensures` of CONVENTIONS §3 on
`(Extracted.program.onlySegments names).link impl`; `sum`: `ens` as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatAdd

def names : List String := LibNatAdd.names

/-- The return site of the self-call. -/
abbrev hSelfRet : Nat := segAddr Extracted.program fn + 0x218

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = yp ∧ s.regs 7 = yl ∧
        s.regs 8 = yc ∧ Pre R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostX 4464 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hpre⟩
  have hsp0 : 4464 ≤ s.sp.toNat := hpre.1.2.1.2.1
  by_cases hyx : yl.toNat ≤ xl.toNat
  · obtain ⟨k, s', hst, hr, hq1, hq2⟩ := body impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc s hpc
      ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hyx, preS_mono (by omega) hpre⟩
    exact ⟨k, s', hst, hr, hq1, postX_mono (by omega) hsp0 hq2⟩
  · have hpre' := hpre
    obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, -, -, -, hx40, hy40, -⟩ := hpre'
    unfold Apart at hga
    janus_run until [segAddr Extracted.program fn + 0x214]
    janus_step
    have hF1 : MemFrame s.mem (((((s.mem.writeLE (s.sp.toNat - 160) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 168) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 zp.toNat).writeLE (s.sp.toNat + 32) 8 xp.toNat).writeLE
        (s.sp.toNat + 56) 8 yp.toNat) (winA s 4464 80) := by simp only [winA]; janus_frame
    refine ReachesRet.call (body impl hap R hmk hmv b L zp zl zc yp yl yc xp xl xc) rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, preS_swap hpre rfl ?_ hF1 (by simp)⟩ ?_
    rotate_left
    all_goals try janus_simp
    intro s2 hpc2 ⟨⟨hs2, h28', h29', h18'⟩, hq⟩
    have hq' := hq
    obtain ⟨_, hmf, _⟩ := hq'
    have e160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hzo : Outside zp.toNat (8 * zc.toNat) (win s 4464 80) := hpre.2.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at hzo
    have hrd : ∀ a, s.sp.toNat - 168 ≤ a → a + 8 ≤ s.sp.toNat - 152 → s2.mem.readLE a 8 =
        (((((s.mem.writeLE (s.sp.toNat - 160) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 168) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 zp.toNat).writeLE (s.sp.toNat + 32) 8 xp.toNat).writeLE
        (s.sp.toNat + 56) 8 yp.toNat).readLE a 8 := by
      intro a ha1 ha2
      refine hmf.readLE _ _ ?_
      simp only [winA, outside_append, outside_cons, outside_nil, and_true, e160]
      and_intros <;> first | exact hout.of_sub (by omega) (by omega) | omega
    have hr1 : s2.mem.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat := by
      rw [hrd _ (by omega) (by omega)]; janus_simp
    have hr2 : s2.mem.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat := by
      rw [hrd _ (by omega) (by omega)]; janus_simp
    janus_run [hr1, hr2]
    exact postX_congr (postX_swap hpre rfl (by janus_simp) hF1 hq) (by janus_simp) (by janus_simp) (by janus_simp) rfl

/-- **`nat.add`** (arm64, exact write set `PostX`): `z.add(x, y)` returns a normalised nat holding `X + Y`, in `z`'s array (`zc ≥ need`) or a
fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ensX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc)
      (PostX 4464 R b L zp zc xp xl yp yl) := by
  rw [show names = LibNatAdd.names from rfl, ← LibNatAdd.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- **`nat.add`** (arm64): `z.add(x, y)` returns a normalised nat holding `X + Y`, in `z`'s array (`zc ≥ need`) or a
fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ensR (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc)
      (fun s s' => Post R b L zp zc xp xl yp yl s s' ∧
        (need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
        (mx xl yl < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40)) :=
  Ensures.mono (ensX impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

/-- (`ensR` without the extra conjuncts.) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc) (Post R b L zp zc xp xl yp yl) :=
  Ensures.mono (ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.NatAdd
