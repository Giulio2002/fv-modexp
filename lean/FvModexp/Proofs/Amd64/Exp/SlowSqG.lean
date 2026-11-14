import FvModexp.Proofs.Amd64.Exp.LibCallsQ
import FvModexp.Proofs.Amd64.Exp.EnsWiden
import FvModexp.Proofs.Amd64.NatQ.SqrRel

set_option autoImplicit false

/-!
# `nat.sqr` (amd64) in an empty-tolerant premise form `SqrE0` (agent expmc s81; twin of Arm64/ExpQ/SlowSqGQ)

Coordinator DECISION 2026-11-14 (1) (consumer-side derivation). amd64 `Q.NatSqr.SPre` needs `accessible xp (8·xl)`
unconditionally, which fails for a `nil` operand; `nat.expNNSlow` may square a `nil` `z` (single-word modulus,
remainder 0). So:
* `SPre0` — the facts the `len x = 0` path needs (`CallEnv`, window, `z`'s liveness, the stack header outside the
  window, the budget, the invariant);
* `SqrE0 impl R ns W` — `P2Pre.SqrE` with the pre `(0 < len x → SPre) ∧ (len x = 0 → SPre0)`, same post `SPost`;
* `zero0` — the `len x = 0` path run directly (`TESTQ R8, R8; JE 0x5f126b`, natmul.go:76-77: spills, `z[:0]` =
  `AX = zp, BX = 0, CX = zc`, `ADDQ $0xa0, SP; POPQ BP; RET`), post from the window frame (`zpost`);
* `sqG hap hsub hsq : SqrE0 impl R ns W` from any `P2Pre.SqrE impl R ns W` (e.g. `CalleeInstQ.sq`) with
  `Q.NatSqr.names ⊆ ns`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

open FvModexp.Amd64.Q.NatSqr (SPre SPost)

/-- the facts of the `len x = 0` path of `z.sqr(stk, x)` -/
def SPre0 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st : Nat) (s : State) : Prop :=
  CallEnv R L s W 64 ∧ sqrW 0 ≤ W ∧ zc < 2 ^ 40 ∧ NatLive s.mem R L zp zc ∧ StkOK s.mem R L st ∧
    Outside st 24 (win s W 64) ∧ sqrCQ 0 + stkR H s.mem st ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- **`nat.sqr` as a callee, empty-tolerant Q-form** (program `ns`, window `W`) -/
def SqrE0 (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (W : Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program Q.NatSqr.fn)
      [zp, zl, zc, st, xp, xl, xc]
      (fun s => (0 < xl.toNat → SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) ∧
        (xl.toNat = 0 → SPre0 R b H L W zp.toNat zc.toNat st.toNat s))
      (fun s s' => SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' ∧
        (xl.toNat = 0 → s'.regs 0 = zp ∧ s'.regs 1 = zc))

set_option maxRecDepth 20000 in
/-- `len x = 0`: the post of `return z[:0]` from a window-only frame -/
theorem zpost {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {W zp zc st xp xc : Nat} {s s' : State}
    (hP : SPre0 R b H L W zp zc st s) (hF : MemFrame s.mem s'.mem (win s W 64)) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (r0 : s'.regs 0 = BitVec.ofNat 64 zp) (r3 : s'.regs 3 = BitVec.ofNat 64 0)
    (r1 : s'.regs 1 = BitVec.ofNat 64 zc) : SPost R b H L W zp zc st xp 0 xc s s' := by
  obtain ⟨hce, hsw, hzc, hzl, hstok, hstw, hcb, hinv⟩ := hP
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : W ≤ (s.regs 4).toNat := by omega
  have hcap : stCap s'.mem st = stCap s.mem st := hF.readLE _ _ (hstw.of_sub (by omega) (by omega))
  have hsb := Q.NatSqr.stackBack_keep hstok hF hstw (LiveExt.refl R L)
  have hv : ∀ (m m' : Memory) (p q : Nat), natVal m' p 0 = natVal m q 0 * natVal m q 0 := by
    intro m m' p q; simp [natVal]
  refine ⟨hfs, hdf, zp, 0, zc, r0, r3, r1, hv _ _ _ _, Or.inl rfl, Nat.zero_le _, Nat.le_refl _, hzc, L, b,
    LiveExt.refl R L, by rw [stkR_congr hcap]; omega,
    Q.NatSqr.inv_frame_win hF hout hW (by decide) hinv, ?_, Or.inl ⟨rfl, rfl⟩,
    fun hn => absurd ⟨rfl, rfl⟩ hn,
    fun _ _ => ⟨rfl, rfl, hv _ _ _ _, hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2,
      Q.NatSqr.lf_win _ hF hLs⟩, hsb,
    hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2, Q.NatSqr.lf_win _ hF hLs⟩
  intro h0; obtain ⟨q1, q2, q3, q4⟩ := hzl h0; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩

/-- the post of the `len x = 0` run (opaque to the run's simp) -/
def ZP (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W : Nat) (zp zc st xp xl xc : BitVec 64) (s s' : State) :
    Prop :=
  SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' ∧
    (xl.toNat = 0 → s'.regs 0 = zp ∧ s'.regs 1 = zc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `len x = 0`: `return z[:0]` (run) -/
theorem zero0 (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) :
    Summary (LibSqr.program.link impl) 6229984
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = zp ∧
        s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = st ∧ s.regs 6 = xp ∧ s.regs 8 = xl ∧ s.regs 9 = xc ∧
        xl.toNat = 0 ∧ SPre0 R b H L W zp.toNat zc.toNat st.toNat s)
      (fun s s' => Q.NatSqr.Kept s s' ∧ ZP R b H L W zp zc st xp xl xc s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hx, hP⟩
  have hce := hP.1
  have hsw := hP.2.1
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, -, -, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxl0 : xl = 0#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl0
  have hZ : ∀ s' : State, MemFrame s.mem s'.mem (win s W 64) → s'.fsBase = s.fsBase → s'.df = s.df →
      s'.regs 0 = zp → s'.regs 3 = BitVec.ofNat 64 0 → s'.regs 1 = zc → ZP R b H L W zp zc st xp 0#64 xc s s' :=
    fun s' hF hfs hd r0 r3 r1 => ⟨zpost hP hF hfs hd (by rw [r0]; simp) r3 (by rw [r1]; simp), fun _ => ⟨r0, r1⟩⟩
  clear hP hsw
  janus64_run [BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hZ _ ?qF ?_ ?_ ?_ ?_ ?_⟩
  case qF => simp only [win]; janus_frame
  all_goals janus64_simp

set_option maxRecDepth 20000 in
/-- `zero0` as an `Ensures` on `nat.sqr`'s own program -/
theorem zeroE (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments Q.NatSqr.names).link impl) (segAddr Extracted.program Q.NatSqr.fn)
      [zp, zl, zc, st, xp, xl, xc]
      (fun s => xl.toNat = 0 ∧ SPre0 R b H L W zp.toNat zc.toNat st.toNat s)
      (fun s s' => SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' ∧
        (xl.toNat = 0 → s'.regs 0 = zp ∧ s'.regs 1 = zc)) := by
  rw [show Q.NatSqr.names = LibSqr.names from rfl, ← LibSqr.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  have hS := zero0 impl R H b L W zp zl zc st xp xl xc
  refine Summary.returns hS hret (by rw [h_rip])
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5,
      h_a6, hpre.1, hpre.2⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- **`SqrE0`** from a non-empty-operand `nat.sqr` summary on `ns ⊇ Q.NatSqr.names` -/
theorem sqG {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hsub : ∀ x, Q.NatSqr.names.contains x = true → ns.contains x = true) {W : Nat}
    (hsq : P2Pre.SqrE impl R ns W) : SqrE0 impl R ns W := by
  intro H b L zp zl zc st xp xl xc ret hret s hs hp
  by_cases hx : xl.toNat = 0
  · exact EnsWiden.ens_widen hap hsub (zeroE impl R H b L W zp zl zc st xp xl xc) ret hret s hs ⟨hx, hp.2 hx⟩
  · exact (hsq H b L zp zl zc st xp xl xc ret hret s hs (hp.1 (Nat.pos_of_ne_zero hx))).mono
      fun s' ⟨ha, hq⟩ => ⟨ha, hq, fun h => absurd h hx⟩

end FvModexp.Amd64.ExpSlow
