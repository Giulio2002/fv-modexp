import FvModexp.Proofs.Arm64.ExpQ.SlowGQ
import FvModexp.Proofs.Arm64.NatQ.SqrHypQ

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowSqG.lean, TIGHT COSTS, agent expmc s43)
# `nat.sqr` (arm64) in the empty-tolerant premise form `ExpSlow.SqrHypG` (agent expmc; consumer-side derivation)

Coordinator DECISION 2026-11-14 (1): derive `SqrHypG` from divmc's existing summary, as infra derived `MulHypG`.
* `len x > 0`: `NatSqr.ens` (`SPre`/`SPost`, window `sqrW 4096`) — `x_preG` builds `SPre` from `SqrPreG ∧ CapIn0 ∧ SqrXG`
  (the operand is then `RdIn`, its capacity positive, and the alias disjunct follows from the guarded `SqrXG` fact);
  the post is divmc's `x_post`.
* `len x = 0` (`n == 0 → return z[:0]`, natmul.go:76; `CBZ R5` at `0x1bb454` → `0x1bb650`): `SPre`'s
  `accessible xp 0` fails for a `nil` operand, so this path is run directly here (`zeroS`): no call, only window stores;
  the result is `z[:0]` (`X0 = zp`, `X1 = 0`, `X2 = zc`), the stack and the live set unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0)
open FvModexp.Arm64.ExpEven (CapIn0)
open FvModexp.Arm64.NatSqr (sqrWX)
open FvModexp.Arm64.Q.NatSqr (SPre SPost)

set_option maxRecDepth 20000 in
/-- `len x > 0`: the `SqrHypG` pre gives divmc's `SPre` -/
theorem x_preGQ {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc : Nat} {s : State}
    (h : SqrPreG R b (sqrCQ xl + stkR H s.mem st) L sqrWX 64 zp zl zc st x xl s) (hc : CapIn0 R L x xl xc)
    (hx : SqrXG R L s sqrWX 64 st zp zc x xl xc) (hH : stLen s.mem st + 4 * (2 * xl) + 64 ≤ H) (hx0 : 0 < xl) :
    SPre R b H L sqrWX zp zc st x xl xc s := by
  obtain ⟨hce, hsv, hglb, -, ⟨hz40, hzl, hzw⟩, ⟨-, hxr⟩, hx12, hal, ⟨hsok, hstw, hstg, hsta⟩, hlen, hza,
    hxa, hcost, hinv⟩ := h
  obtain ⟨-, hxacc, -, -, hxw⟩ := hxr hx0
  obtain ⟨hxc, hxc40, hxh⟩ := hc
  obtain ⟨hxh, hx48⟩ := hxh (by omega)
  obtain ⟨⟨hst0, hswb, hfh, hfw, hfg, hsf, hsgA, hfgA⟩, hzo, hzx, hzop, hxop⟩ := hx
  have hro : RoOut R := hce.2.2.2.2.2.2.2
  refine ⟨hce, by unfold sqrWX sqrW ksqrW; omega, hsv, hglb, NatSqr.wordT_rt hro, hxc, hxc40, hx12, hxacc,
    fun _ => ⟨hxh, hx48⟩, fun _ => hxw, hz40, hzl, hzo, fun h0 => ⟨(hzw h0).2, ?_, (hzop (by omega)).1, (hzop (by omega)).2⟩,
    ?_, ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩, fun h0 => ⟨?_, (hxop (by omega)).1,
    (hxop (by omega)).2⟩, hlen, ⟨hH, hcost⟩, hinv⟩
  · exact (hza (by omega)).1.symm
  · by_cases he : zp = x
    · by_cases hz0 : 0 < zc
      · exact Or.inl ⟨he, hzx he hz0 hx0⟩
      · exact Or.inr fun h1 => absurd h1 hz0
    · rcases hal with h1 | h1
      · exact absurd h1 he
      · exact Or.inr h1
  · exact (hxa (by omega)).1.symm

set_option maxRecDepth 20000 in
/-- `len x = 0`: the post of `return z[:0]` from a window-only frame -/
theorem zpostQ {R : RtInv} {H b c : Nat} {L : List (Nat × Nat)} {zp zl zc st x : Nat} {s s' : State}
    (h : SqrPreG R b (c + stkR H s.mem st) L sqrWX 64 zp zl zc st x 0 s) (hF : MemFrame s.mem s'.mem (winA s sqrWX 64))
    (r0 : s'.regs 0 = BitVec.ofNat 64 zp) (r1 : s'.regs 1 = 0#64) (r2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    SqrPostQ R b (c + stkR H s.mem st) (stkR H s'.mem st) L sqrWX 64 zp zc st x 0 s s' := by
  obtain ⟨hce, -, -, -, ⟨hz40, hzl, -⟩, -, -, -, ⟨hsok, hstw, -, -⟩, -, -, -, hcb, hinv⟩ := h
  obtain ⟨-, ⟨-, hw, -, -⟩, -, hout, -, -, hLs, -⟩ := hce
  have hLF : ∀ ws, LiveFrame s.mem s'.mem L ws := fun ws => NatSqr.lf_win ws hF hLs
  have hsw : Outside st 24 (winA s sqrWX 64) := by
    simp only [win, winA, outside_cons, outside_nil, and_true] at hstw ⊢; omega
  have hcap : stCap s'.mem st = stCap s.mem st := hF.readLE _ _ (hsw.of_sub (by omega) (by omega))
  refine ⟨zp, 0, zc, r0, by rw [r1], r2, L, b, ⟨by simp, Or.inl rfl, Nat.zero_le _, hz40, ?_, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨LiveExt.refl R L, by rw [stkR_congr hcap]; omega, inv_frame_winA hF hout (by unfold sqrWX sqrW ksqrW at hw ⊢; omega)
      (by decide) hinv⟩,
    NatSqr.stackBack_keep hsok hF hsw (LiveExt.refl R L), fun hn => absurd ⟨rfl, rfl⟩ hn,
    hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2, hLF _⟩
  intro h0; obtain ⟨q1, q2, q3, q4⟩ := hzl h0; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `len x = 0`: `return z[:0]` (run) -/
theorem zeroSQ (impl : List Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat))
    (zp zl zc st xp xl xc : BitVec 64) :
    Summary (LibSqr.program.link impl) 0x1bb420
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = st ∧ s.regs 4 = xp ∧ s.regs 5 = xl ∧ s.regs 6 = xc ∧ xl.toNat = 0 ∧
        SqrPreG R b (sqrCQ xl.toNat + stkR H s.mem st.toNat) L sqrWX 64 zp.toNat zl.toNat zc.toNat st.toNat xp.toNat
          xl.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        SqrPostQ R b (sqrCQ xl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L sqrWX 64 zp.toNat zc.toNat
          st.toNat xp.toNat xl.toNat s s' ∧ (xl.toNat = 0 → s'.regs 0 = zp ∧ s'.regs 2 = zc)) := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hx, hpre⟩
  have hxl0 : xl = 0#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl0
  have hP : SqrPreG R b (sqrCQ 0 + stkR H s.mem st.toNat) L sqrWX 64 zp.toNat zl.toNat zc.toNat st.toNat xp.toNat 0 s :=
    hpre
  clear hpre
  have hce := hP.1
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hce
  have hW : 4880 ≤ sqrWX := by unfold sqrWX sqrW ksqrW; omega
  have hZ : ∀ s' : State, MemFrame s.mem s'.mem (winA s sqrWX 64) → s'.regs 0 = BitVec.ofNat 64 zp.toNat →
      s'.regs 1 = 0#64 → s'.regs 2 = BitVec.ofNat 64 zc.toNat →
      SqrPostQ R b (sqrCQ 0 + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L sqrWX 64 zp.toNat zc.toNat st.toNat
        xp.toNat 0 s s' := fun s' hF r0 r1 r2 => zpostQ hP hF r0 r1 r2
  clear hP
  generalize stkR H = f at hZ ⊢
  janus_run
  exact hZ _ (by simp only [winA]; janus_frame) (by janus_simp) (by janus_simp) (by janus_simp)

set_option maxRecDepth 20000 in
/-- **`nat.sqr`** (arm64) in the empty-tolerant Q-form premise `SqrHypGQ`, window `sqrW 4096`, `above = 64`, cost `sqrCQ` -/
theorem sqrGQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    SqrHypGQ impl R NatSqr.names sqrWX 64 sqrCQ := by
  intro H b L z zl zc st x xl xc ret hret s hs hp
  by_cases hx : xl.toNat = 0
  · rw [show NatSqr.names = LibSqr.names from rfl, ← LibSqr.eq_only] at hret hs ⊢
    janus_intro hs
    have hr48 := hret.user
    have hr4 := hret.aligned
    have hS := zeroSQ impl R H b L z zl zc st x xl xc
    have e4 : (s.regs 30).toNat % 4 = 0 := by
      rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
    have e48 : (s.regs 30).toNat < 2 ^ 48 := by
      rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48
    exact Summary.returns hS hret h_pc h_lr ⟨e4, e48, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, hx, hp.1⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · have hx0 : 0 < xl.toNat := Nat.pos_of_ne_zero hx
    exact (Q.NatSqr.ens impl hap R hmk hgr hmc hmv hwb H b L sqrWX z zl zc st x xl xc ret hret s hs
      (x_preGQ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hx0)).mono fun s' hq => ⟨hq.1, (Q.NatSqr.q_post hq.2).1, fun h => absurd h hx⟩

end FvModexp.Arm64.Q.ExpSlow
