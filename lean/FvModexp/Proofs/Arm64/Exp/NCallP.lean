import FvModexp.Proofs.Arm64.Exp.NPost
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.expNN` (arm64): the pure post of a callee path (`rem`, `expNNSlow`, `expNNPowerOfTwo`)

`post_call`: from the callee's `NHyp.CPost` (at the callee entry `S`, live set `L1`, budget `b1`, `z` argument
`(zq, zcq)`) and the epilogue's frame (the result slots `SP' + 176..200`), `ExpN.Post` at the entry `s`. Inputs: the
memory before the call changed only in the runtime ranges and the window (`R.rt ++ wN`), live objects untouched,
`L ⊆ L1` (`LiveExt`), `b - mk ≤ b1`, `z` argument empty / the entry's `z` (apart from the window) / fresh w.r.t. `L`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- the `z` argument of a callee: empty, the entry's `z` (apart from the window), or a fresh runtime block -/
@[reducible] def ZArg (R : RtInv) (L : List (Nat × Nat)) (sp K zp zc zq zcq : Nat) : Prop :=
  (zcq = 0 ∧ (zq = 0 ∨ (zq = zp ∧ zc = 0))) ∨ (zq = zp ∧ zcq = zc ∧ Apart zp (8 * zc) (sp - K) (K + 1432)) ∨
    (InRanges zq (8 * zcq) R.rt ∧ ApartAll zq (8 * zcq) L)

theorem apartAll_ext {R : RtInv} {L L1 : List (Nat × Nat)} {a k : Nat} (hx : LiveExt R L L1) (h : ApartAll a k L1) :
    ApartAll a k L := fun r hr => h r (hx.mem_old hr)

/-- a memory frame, byte-wise weakened (empty ranges drop out) -/
theorem mf_byte {m m' : Memory} {ws ws' : List (Nat × Nat)} (h : MemFrame m m' ws)
    (hw : ∀ x, Outside x 1 ws' → Outside x 1 ws) : MemFrame m m' ws' :=
  ⟨fun a n ho => Memory.readLE_congr fun i hi => by
      have := h.readLE (a + i) 1 (hw _ (ho.of_sub (by omega) (by omega)))
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this, h.accessible⟩

/-- the callee post `post_call` consumes (`NHyp.CPost` and `ExpOdd.Post` both give it): result old or fresh, `StackBackL` -/
@[reducible] def CPostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (natVal s'.mem p l = v ∧ NatNorm s'.mem p l ∧ l ≤ c ∧ (c < 2 ^ 40 ∧ p < 2 ^ 64) ∧
      NatLive s'.mem R L' p c ∧ ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L))) ∧
      ExpHyp.RtPost R b cst L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧ ResSep s.mem s'.mem st p c

theorem cpostG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zc st v cst : Nat} {s s' : State}
    (hz : zp < 2 ^ 64) (h : NHyp.CPostR R b L stk above zp zc st v cst s s') :
    CPostG R b L stk above zp zc st v cst s s' := by
  obtain ⟨p, l, c, q0, q1, q2, L', b', ⟨hval, hnorm, hlc, hc40, hlive, hof⟩, hrt, hsb, hF, hLF, hRS⟩ := h
  have hp : p < 2 ^ 64 := by
    rcases hof with ⟨rfl, -⟩ | ⟨h1, -⟩
    · exact hz
    · have := (hlive (by omega)).2.2.2; omega
  exact ⟨p, l, c, q0, q1, q2, L', b', ⟨hval, hnorm, hlc, ⟨hc40, hp⟩, hlive,
    hof.imp id (fun h => ⟨h.2.1, h.2.2⟩)⟩, hrt, hsb, hF, hLF, hRS⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem post_call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n : Nat} {s S s' s'' : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq stk v cst mk : Nat}
    (hs : s.sp.toNat = sp + 1312) (hK : K ≤ sp) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 1432))
    (hF0 : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF0 : LiveFrame s.mem S.mem L [])
    (hx1 : LiveExt R L L1) (hb1 : b - mk ≤ b1) (hzq : ZArg R L sp K zp zc zq zcq)
    (hSsp : S.sp.toNat = sp + 1056) (hstk : stk ≤ K + 1056) (h28 : S.regs 28 = s.regs 28)
    (hv : v = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n)
    (hC : mk + cst ≤ NCost costF costR costS costP xl yl n (stLen s.mem st) (Nat.log2 (natVal s.mem mp n)))
    (hq : CPostG R b1 L1 stk 112 zq zcq st v cst S s')
    (hfin : MemFrame s'.mem s''.mem [(sp + 1232, sp + 1256)])
    (e0 : s''.regs 0 = s'.regs 0) (e1 : s''.regs 1 = s'.regs 1) (e2 : s''.regs 2 = s'.regs 2) :
    Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s'' := by
  obtain ⟨p, l, c, q0, q1, q2, L', b', ⟨hval, hnorm, hlc, hc40, hlive, hof⟩, ⟨hx2, hb2, hinv⟩, ⟨⟨k1, k2, k3⟩, k4⟩,
    hF, hLF, hRS⟩ := hq
  have hw := out_rt_wN hrw
  have hwrt : Outside (sp - K) (K + 1304) R.rt := by
    have := hw (sp - K, sp + 1304) (List.mem_cons_self ..)
    simp only at this; rwa [show sp + 1304 - (sp - K) = K + 1304 by omega] at this
  -- the stack header: unchanged from `s` to `S`
  have hstO : Outside st 24 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_mk (hH.elim (fun h => Or.inl (h.sub (by omega) (by omega))) (fun h => Or.inr (h.of_sub (by omega) (by omega))))
      hLF0 hF0 (hstO.of_sub (by omega) (by omega))
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have hws : stkWs S.mem st = stkWs s.mem st := by simp only [stkWs, ew, el, ec]
  -- the epilogue slots
  have hslot : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1304) → Outside a k [(sp + 1232, sp + 1256)] := fun h => by
    unfold Apart at h; simp only [outside_cons, outside_nil, and_true]; omega
  have hst'' : Outside st 24 [(sp + 1232, sp + 1256)] := hslot (by unfold Apart at hstw ⊢; omega)
  obtain ⟨k1', -, el', -⟩ := stkOK_frame k1 hfin hst'' (LiveExt.refl R L')
  -- the result's array is apart from the window
  have hres : 0 < c → Apart p (8 * c) (sp - K) (K + 1304) := by
    intro hc
    rcases hof with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · rcases hzq with ⟨h0, -⟩ | ⟨e1, e2, hzw⟩ | ⟨hin, -⟩
      · omega
      · rw [e1, e2]; unfold Apart at hzw ⊢; omega
      · have := out_inR2 hwrt hin; unfold Apart; omega
    · have := out_inR2 hwrt hin; unfold Apart; omega
  have hvn : natVal s''.mem p l = natVal s'.mem p l ∧ NatNorm s''.mem p l := by
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0; exact ⟨rfl, Or.inl rfl⟩
    · have hpl : Outside p (8 * l) [(sp + 1232, sp + 1256)] := by
        have := hres (by omega); unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
      exact ⟨hfin.readLE _ _ hpl, ExpOdd.norm_fr hfin hpl hnorm⟩
  refine ⟨p, l, c, e0.trans q0, e1.trans q1, e2.trans q2, ?_, hvn.2, hlc, hc40,
    L', b', hx1.trans hx2, by omega, ?_, natLive_frame hlive (LiveExt.refl R L') hfin, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hv, ← hval]; exact hvn.1
  · rw [← h28]
    exact Expmc.inv_frame hfin (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Or.inr (hwrt.of_sub (by simp only; omega) (by simp only; omega))) hinv
  · rcases hof with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · rcases hzq with ⟨h0, rfl | ⟨rfl, hz0⟩⟩ | ⟨h1, h2, -⟩ | ⟨hin, hap⟩
      · exact Or.inl ⟨h0, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, h0.trans hz0.symm⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hin, hap⟩)
    · exact Or.inr (Or.inr ⟨hin, apartAll_ext hx1 hap⟩)
  · have e3 := stkOK_frame k1 hfin hst'' (LiveExt.refl R L')
    refine ⟨⟨k1', el'.trans (k2.trans el), ?_⟩, ?_⟩
    · rw [e3.2.1, e3.2.2.2]
      rcases k3 with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact Or.inl ⟨a1.trans ew, a2.trans ec⟩
      · exact Or.inr ⟨a1, apartAll_ext hx1 a2⟩
    · intro hn; rw [e3.2.1, e3.2.2.2] at hn ⊢; exact k4 (by rw [ew, ec]; exact hn)
  · have h3 : MemFrame s.mem s''.mem ((R.rt ++ wN sp K) ++ ((R.rt ++ winA S stk 112 ++ [(zq, zq + 8 * zcq)] ++
        ExpHyp.stWs S.mem st) ++ [(sp + 1232, sp + 1256)])) :=
      hF0.trans (hF.trans hfin fun a k ho => by rw [outside_append] at ho; exact ho)
        fun a k ho => by rw [outside_append] at ho; exact ho
    refine mf_byte h3 fun x ho => ?_
    rw [outside_append, outside_append, outside_append] at ho
    obtain ⟨⟨⟨hr, hw1⟩, hz⟩, hst⟩ := ho
    simp only [winA, hs, stkWs, outside_cons, outside_nil, and_true] at hw1 hz hst
    have hzx : Outside x 1 [(zq, zq + 8 * zcq)] := by
      simp only [outside_cons, outside_nil, and_true]
      rcases hzq with ⟨h0, -⟩ | ⟨e1, e2, -⟩ | ⟨hin, -⟩
      · rw [h0]; omega
      · rw [e1, e2]; exact hz
      · have := out_inR2 hr hin; omega
    simp only [ExpHyp.stWs, stkWs, ew, el, ec, wN, winA, hSsp, outside_append, outside_cons, outside_nil, and_true]
    simp only [outside_cons, outside_nil, and_true] at hzx
    exact ⟨⟨hr, by omega, by omega⟩, ⟨⟨⟨hr, by omega, by omega⟩, hzx⟩, by omega, by omega⟩, by omega⟩
  · refine ⟨fun a k hin hout => Memory.readLE_congr fun i hi => ?_⟩
    have hin1 : InRanges (a + i) 1 L := hin.sub (by omega) (by omega)
    have hout1 : Outside (a + i) 1 ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) := hout.of_sub (by omega) (by omega)
    obtain ⟨q, hq, e1q, e2q⟩ := hin1
    have hq1 := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at hq1
    have r1 := hfin.readLE (a + i) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have r2 := hLF.readLE (a + i) 1 (hx1.inRanges_old ⟨q, hq, e1q, e2q⟩) (by
      simp only [ExpHyp.stWs]; rw [hws]
      simp only [outside_append, outside_cons, outside_nil, and_true] at hout1 ⊢
      refine ⟨?_, hout1.2⟩
      rcases hzq with ⟨h0, -⟩ | ⟨e1, e2, -⟩ | ⟨-, hap⟩
      · rw [h0]; omega
      · rw [e1, e2]; exact hout1.1
      · have := hap q hq; unfold Apart at this; omega)
    have r3 := hLF0.readLE (a + i) 1 ⟨q, hq, e1q, e2q⟩ trivial
    simp only [Memory.readLE_one] at r1 r2 r3
    exact BitVec.eq_of_toNat_eq (r1.trans (r2.trans r3))
  · have e3 := stkOK_frame k1 hfin hst'' (LiveExt.refl R L')
    exact ResSep.congr (ResSep.pre hRS ew ec) e3.2.1 e3.2.2.2

end FvModexp.Arm64.ExpN
