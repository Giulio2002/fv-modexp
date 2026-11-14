import FvModexp.Proofs.Amd64.Exp.P2DDefs
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): transport of the entry facts to a callee one frame down, and back (agent asm s67;
amd64 twin of infra's arm64 `P2DT`, modelled on expmc's `Amd64/Exp/NCPre.cpre_at`)

Entry `s` (`RSP = E`, `[E]` = return address); the function's frame is `sp = E - 0x70`, and every callee is entered
at `RSP_S = sp - 8 = E - 0x78` (the `CALL` pushes its return address at `[sp - 8]`). Frame facts: the callee memory
`S.mem` is the entry memory changed only in the runtime ranges and `ownW s stk A` (the entry window without the
return-address word), live objects untouched.
* `cenv_ent`: the entry `CallEnv` as a `CallW.CEnv` (`sp = RSP`, `K = stk`);
* `cpre_sub`: `NHyp.CPre` at a callee entry (window `[RSP_S - stk', RSP_S + A')`, `stk' + 0x78 ≤ stk`, `A' ≤ 0x78`)
  from the entry `NHyp.CPre` (the inputs supplied separately: `in_sub` for an entry input);
* `cpost_pre`: a callee's `NHyp.CPostR` (relative to `S`) is ours (relative to the entry `s`);
* `natOne_sub`: the `natOne` facts one frame down.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

/-- the ranges the function itself may write (the entry window without the return-address word `[RSP, RSP + 8)`) -/
@[reducible] def ownW (s : State) (stk A : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - stk, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + A)]

theorem hdr_eq {R : RtInv} {L : List (Nat × Nat)} {st : Nat} {m M : Memory} {ws : List (Nat × Nat)}
    (hH : Held R L st 24) (hF : MemFrame m M (R.rt ++ ws)) (hLF : LiveFrame m M L []) (ho : Outside st 24 ws) :
    stW M st = stW m st ∧ stLen M st = stLen m st ∧ stCap M st = stCap m st := by
  have rd : ∀ o, o + 8 ≤ 24 → M.readLE (st + o) 8 = m.readLE (st + o) 8 := fun o hlt =>
    (hH.sub (by omega) (by omega)).readLE hF (LiveFrame.of_nil' hLF ws) (ho.of_sub (by omega) (by omega))
  exact ⟨by have := rd 0 (by omega); simpa using this, rd 8 (by omega), rd 16 (by omega)⟩

/-- a read through a frame whose ranges are each empty or apart from the read -/
theorem rd_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a k : Nat}
    (ho : ∀ r ∈ rs, r.2 ≤ r.1 ∨ a + k ≤ r.1 ∨ r.2 ≤ a) : m'.readLE a k = m.readLE a k := by
  refine Janus.Arm64.Memory.readLE_congr fun j hj => ?_
  have h1 := h.readLE (a + j) 1 (outside_of_forall fun r hr => by
    rcases ho r hr with q | q | q <;> omega)
  simp only [Janus.Arm64.Memory.readLE_one] at h1
  exact BitVec.eq_of_toNat_eq h1

/-- `CEnv` with an extended live set (copy of expmc's `ExpN.cenv_ext`) -/
theorem cenv_ext {R : RtInv} {L L1 : List (Nat × Nat)} {g fs sp K A : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs sp K A M) (hx : LiveExt R L L1) : CallW.CEnv R L1 g fs sp K A M := by
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hx.liveSep hLs fun r hr => ?_, hd, hro, f1, f2, f3, f4,
    f5, f6⟩
  simp only [List.mem_singleton] at hr; subst hr; simp only
  rwa [show sp + A - (sp - K) = K + A by omega]

/-- a `CEnv` at a lower base inside the same window (copy of expmc's `ExpOdd.cenv_rebase`) -/
theorem cenv_rebase {R : RtInv} {L : List (Nat × Nat)} {g fs x K A x' K' A' : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs x K A M) (e : x' - K' = x - K) (hK' : K' ≤ x') (hA : x' + A' ≤ x + A)
    (hal : x' % 8 = 0) : CallW.CEnv R L g fs x' K' A' M := by
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨hal, hK', by omega, M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega), hg1, hg2,
    by omega, hrt.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgrt, ?_, hd, hro, f1, f2, f3, f4, f5,
    by unfold Apart at f6 ⊢; omega⟩
  intro r hr
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- the entry `CallEnv` as a `CEnv` -/
theorem cenv_ent {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk A : Nat} (h : CallEnv R L s stk A) :
    CallW.CEnv R L (s.regs 14).toNat s.fsBase.toNat (s.regs 4).toNat stk A s.mem := by
  obtain ⟨hgd, ⟨hle, h48, hacc⟩, hal, hdl, hwrt, hgw, hgrt, hLs, hro, ⟨htb, htr, htg⟩, htout, htap⟩ := h
  obtain ⟨gnw, grd, gbl⟩ := hgd
  simp only [regSP, regG, stackguard0, stackguard0Offset] at gnw grd gbl hle h48 hacc htg htb
  exact ⟨hal, hle, h48, hacc, by omega, grd, by omega, hwrt, hgw, hgrt, hLs, hdl, hro, by omega, by omega, htr, htg,
    htout, htap⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s S : State}

theorem win_out {a k stk' A' : Nat} (h : Outside a k (win s stk A)) (hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat)
    (hk : stk' + 0x78 ≤ stk) (hA : A' ≤ 0x78) : Outside a k (win S stk' A') := by
  simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega

theorem own_of {a k : Nat} (h : Outside a k (win s stk A)) : Outside a k (ownW s stk A) := by
  simp only [win, ownW, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- an entry input's facts at the callee entry -/
theorem in_sub (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {p n : Nat} (hpn : (p, n) ∈ ins)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1)
    (hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat) {stk' A' : Nat} (hk : stk' + 0x78 ≤ stk) (hA : A' ≤ 0x78) :
    EvenHyp.RdIn R L1 S stk' A' p n ∧ n ≤ 2 ^ 9 ∧ NatNorm S.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (NHyp.freeOf S.mem st).1 (NHyp.freeOf S.mem st).2 ∧ (0 < zc → Apart zp (8 * zc) p (8 * n)) := by
  obtain ⟨-, -, -, -, -, -, -, hins, hsok, hstw, -⟩ := hP
  obtain ⟨⟨h40, hacc, h48, hH, hw⟩, hn, hN, hst, hfr, hz⟩ := hins p n hpn
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF (own_of hstw)
  refine ⟨⟨h40, by rw [hF.accessible]; exact hacc, h48, hx.held hH, win_out hw hSsp hk hA⟩, hn, ?_, hst, ?_, hz⟩
  · rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · exact Or.inl hn0
    rcases hN with h0 | h1
    · exact Or.inl h0
    · right
      rw [(hH.sub (a := p + 8 * (n - 1)) (n := 8) (by omega) (by omega)).readLE hF (LiveFrame.of_nil' hLF _)
        (own_of (hw.of_sub (by omega) (by omega)))]; exact h1
  · show Apart p (8 * n) (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`NHyp.CPre` at a callee entry one frame down** (inputs supplied) -/
theorem cpre_sub (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    (hrg : S.mem.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} {b1 : Nat} (hx : LiveExt R L L1)
    (hinv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 S.mem))
    (hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    {stk' A' : Nat} (hk : stk' + 0x78 ≤ stk) (hA : A' ≤ 0x78) {ins' : List (Nat × Nat)} {need' cst' : Nat}
    (hins : ∀ p n, (p, n) ∈ ins' → EvenHyp.RdIn R L1 S stk' A' p n ∧ n ≤ 2 ^ 9 ∧ NatNorm S.mem p n ∧
      Apart p (8 * n) st 24 ∧ Apart p (8 * n) (NHyp.freeOf S.mem st).1 (NHyp.freeOf S.mem st).2 ∧
      (0 < zc → Apart zp (8 * zc) p (8 * n)))
    (hneed : stLen s.mem st + need' ≤ 2 ^ 16) (hcst : cst' ≤ b1) :
    NHyp.CPre R b1 L1 stk' A' zp zl zc st ins' need' cst' S := by
  obtain ⟨hce, hsv, hgl, hro, hwT, hzl, hwo, -, hsok, hstw, hstg, harr, hcap0, -, hwba, hstwb, hstf,
    ⟨hstfs, hfrfs⟩, hzs, hstgA, hfgA, -, hadx, harrfs, -⟩ := hP
  have ce0 := cenv_ent hce
  have hSg : (S.regs 14).toNat = (s.regs 14).toNat := by rw [h14]
  have hSf : S.fsBase.toNat = s.fsBase.toNat := by rw [hfs]
  generalize hSP : (s.regs 4).toNat = SP at *
  generalize hG : (s.regs 14).toNat = g at *
  generalize hFS : s.fsBase.toNat = fs at *
  have ho : ∀ {a k : Nat}, Outside a k (win s stk A) → Outside a k (ownW s stk A) := own_of
  have hwin : ∀ {a k : Nat}, Outside a k (win s stk A) → Outside a k (win S stk' A') := fun h =>
    win_out h (by rw [hSP]; exact hSsp) hk hA
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF (ho hstw)
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hrt, hga, hgrt, -, -, -, -, -, -, -, f5, f6⟩ := id ce0
  -- the call environment
  have hws : ∀ r ∈ ownW s stk A, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;>
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have ce1 := CallW.CEnv.frame ce0 hF hrg hws
    (by unfold Apart at hga; simp only [ownW, hSP, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [ownW, hSP, outside_cons, outside_nil, and_true]; omega)
  have ce2 := cenv_ext (cenv_rebase ce1 (x' := SP - 0x78) (K' := stk - 0x78) (A' := 0x78 + A) (by omega)
    (by omega) (by omega) (by omega)) hx
  have hcall := CallW.callEnv_of ce2 (by omega) hSg hSf rfl (stk := stk') (above := A') (by omega) (by omega)
    (by omega)
  -- the globals
  have hgl' : RunIface.Globals R S.mem (win S stk' A') := by
    obtain ⟨q40, q12, q80, q40', e8, e16, e24, hgacc, hgrt', hgw', hwbacc, hwbrt, hwbw⟩ := hgl
    have hgA : Outside RunIface.gA 32 (R.rt ++ ownW s stk A) := by rw [outside_append]; exact ⟨hgrt', ho hgw'⟩
    have hrd : ∀ k, k + 8 ≤ 32 → S.mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 := fun k hk =>
      hF.readLE _ _ (hgA.of_sub (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt', hwin hgw',
      by rw [hF.accessible]; exact hwbacc, hwbrt, hwin hwbw⟩
    · rw [e8, hrd 8 (by omega), ← e8]; exact q40
    · rw [e16, hrd 16 (by omega), ← e16]; exact q12
    · rw [e24, hrd 24 (by omega), ← e24]; exact q80
    · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
      show S.mem.readLE RunIface.gA 8 = 40; rw [this]; exact q40'
  obtain ⟨hz40, hzL, hzW⟩ := hwo
  refine ⟨hcall, hsv, hgl', hro, hwT, hzl, ⟨hz40, fun hc => ?_, fun hc => ?_⟩, hins, stkOK_hdr hsok hF ew el ec hx,
    hwin hstw, by rw [hSg]; exact hstg, ?_, by rw [ec, ew]; exact hcap0, by rw [el]; exact hneed,
    by rw [hF.accessible]; exact hwba, hstwb, ?_, ⟨by rw [hSf]; exact hstfs, ?_⟩, fun hc => ?_, hstgA, ?_, hcst,
    by rw [hF.accessible]; exact hadx, ?_, by rw [hSg]; exact hinv⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hzL hc
    exact ⟨a1, hx.held a2, by rw [hF.accessible]; exact a3, a4⟩
  · obtain ⟨a1, a2, a3⟩ := hzW hc
    exact ⟨hwin a1, by rw [hSg, ← hG]; exact a2, by rw [hSf, ← hFS]; exact a3⟩
  · rw [ec, ew, hSg]; intro hc
    obtain ⟨a1, a2⟩ := harr hc
    exact ⟨hwin a1, a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hstf
  · show Apart (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st)) (S.fsBase.toNat - 8) 8
    rw [ew, el, ec, hSf]; exact hfrfs
  · obtain ⟨a1, a2, a3⟩ := hzs hc
    refine ⟨a1, ?_, a3⟩
    show Apart zp (8 * zc) (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact a2
  · show Apart (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st)) RunIface.gA 32
    rw [ew, el, ec]; exact hfgA
  · rw [ec, ew, hSf]; exact harrfs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **a callee's exit facts one frame down are ours** -/
theorem cpost_pre (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} {b1 : Nat} (hx : LiveExt R L L1)
    (hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    (hdf : S.df = s.df) {stk' A' : Nat} (hk : stk' + 0x78 ≤ stk) (hA : A' ≤ 0x78) {v cst' : Nat}
    (hb : b - cst ≤ b1 - cst')
    {S' s' : State} (hq : NHyp.CPostR R b1 L1 stk' A' zp zc st v cst' S S')
    (hm : s'.mem = S'.mem) (e0 : s'.regs 0 = S'.regs 0) (e3 : s'.regs 3 = S'.regs 3) (e1 : s'.regs 1 = S'.regs 1)
    (efs : s'.fsBase = S'.fsBase) (edf : s'.df = S'.df) :
    NHyp.CPostR R b L stk A zp zc st v cst s s' := by
  have hsok := hP.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ew, el, ec⟩ := hdr_eq hsok.2.1 hF hLF (own_of hstw)
  obtain ⟨qfs, qdf, p, l, c, q0, q3, q1, L', b', ⟨hv, hn, hlc, hc40, hlive, hor⟩, ⟨hx', hb', hinv⟩,
    ⟨⟨hsk, hsl, hkf⟩, hai⟩, hF', hLF', hrs⟩ := hq
  have hsub : ∀ {a k : Nat}, ApartAll a k L1 → ApartAll a k L := fun h r hr => h r (hx.mem_old hr)
  refine ⟨efs.trans (qfs.trans hfs), edf.trans (qdf.trans hdf), p, l, c, e0.trans q0, e3.trans q3, e1.trans q1, L', b',
    ?_, ⟨hx.trans hx', by omega, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact ⟨hv, hn, hlc, hc40, hlive, hor.imp id fun h => ⟨h.1, h.2.1, hsub h.2.2⟩⟩
  · rw [hm, ← h14]; exact hinv
  · rw [hm]
    refine ⟨⟨hsk, by rw [hsl, el], ?_⟩, ?_⟩
    · rw [ew, ec] at hkf; exact hkf.imp id fun h => ⟨h.1, hsub h.2⟩
    · intro hn'; apply hai; rw [ew, ec]; exact hn'
  · rw [hm]
    have es : stWs S.mem st = stWs s.mem st := by unfold stWs stkWs; rw [ew, el, ec]
    rw [es] at hF'
    refine hF.trans hF' fun a k hok => ?_
    simp only [win, ownW, outside_append, outside_cons, outside_nil, and_true] at hok ⊢
    refine ⟨⟨hok.1.1.1, by omega, by omega⟩, ⟨⟨hok.1.1.1, by omega⟩, hok.1.2⟩, hok.2⟩
  · rw [hm]
    refine (LiveFrame.of_nil' hLF _).trans ?_ fun a k h => hx.inRanges_old h
    simp only [stWs, stkWs, ew, el, ec] at hLF'
    exact hLF'
  · rw [hm]; exact hrs.pre ew ec

/-- the `natOne` facts at a callee entry one frame down -/
theorem natOne_sub {op : Nat}
    (hone : EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st))
    (hsa : NHyp.StkApart s.mem st op 8)
    (hF : MemFrame s.mem S.mem (ownW s stk A)) {L1 : List (Nat × Nat)} (hx : LiveExt R L L1)
    (hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat) {stk' A' : Nat} (hk : stk' + 0x78 ≤ stk) (hA : A' ≤ 0x78)
    (ew : stW S.mem st = stW s.mem st) (el : stLen S.mem st = stLen s.mem st) (ec : stCap S.mem st = stCap s.mem st) :
    EvenHyp.NatOne R L1 S.mem op (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) ∧
      NHyp.StkApart S.mem st op 8 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hone
  have es : stWs S.mem st = stWs s.mem st := by unfold stWs stkWs; rw [ew, el, ec]
  have hwo : ∀ {a k : Nat}, Outside a k (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (ownW s stk A) := fun h => by
    simp only [win, ownW, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hww : ∀ {a k : Nat}, Outside a k (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) := fun h => by
    rw [es]; simp only [win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨⟨by omega, h.1.2⟩, h.2⟩
  have rd : ∀ k, k + 8 ≤ 24 → S.mem.readLE (EvenHyp.natOneA + k) 8 = s.mem.readLE (EvenHyp.natOneA + k) 8 :=
    fun k hk => hF.readLE _ _ ((hwo n7).of_sub (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, by rw [hF.readLE _ _ (hwo n11)]; exact n4, by rw [hF.accessible]; exact n5, n6, hww n7,
    by rw [hF.accessible]; exact n8, n9, hx.held n10, hww n11⟩, ?_⟩
  · have := rd 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact n1
  · rw [rd 8 (by omega)]; exact n2
  · rw [rd 16 (by omega)]; exact n3
  · intro h; obtain ⟨a1, a2⟩ := hsa h
    refine ⟨a1, fun hl => ?_⟩
    rw [el, ec] at hl; rw [ew, el, ec]; exact a2 hl

end

end FvModexp.Amd64.P2D
