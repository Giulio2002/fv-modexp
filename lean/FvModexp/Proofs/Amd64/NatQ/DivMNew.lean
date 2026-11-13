import FvModexp.Proofs.Amd64.NatQ.DivMJoin

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, the pool was empty: `newobject(type:big.stack)` (nat.go:289) (top s41)

Twin of Arm64/NatQ/DivMNew.lean (`noPreD` / `NewND` / `noCallD` / `newStk_ND`) on `nat.div`'s amd64 frame
(entry `RSP = sp`, callee entry `RSP = sp - 240`, window `[sp - 41512, sp + 112)`). The descriptor `type:big.stack`
(`stkTy`, data object 4): `StkTyData.stkTy_data`, `apart_of_data hd 4`, `RoOut.out' _ 4`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

theorem blockSize_stk24 : blockSize 24 false = 24 := by decide

theorem cs_new {s X : State} (esp : (X.regs 4).toNat = (s.regs 4).toNat - 240) (hb : 41512 ≤ (s.regs 4).toNat) :
    calleeStack64 X 4096 1 = [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
      ((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)] := by
  simp only [calleeStack64, esp]
  rw [show (s.regs 4).toNat - 240 + 8 = (s.regs 4).toNat - 232 by omega,
    show (s.regs 4).toNat - 232 + 8 * 1 = (s.regs 4).toNat - 224 by omega]

set_option maxRecDepth 20000 in
/-- the descriptor words at the `newobject` entry -/
theorem stkTy_at {R : RtInv} {L : List (Nat × Nat)} {s X : State} (hce : CallEnv R L s 41512 112)
    (hXF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112)) :
    X.mem.accessible 7357344 16 false = true ∧ X.mem.readLE 7357344 8 = 24 ∧ X.mem.readLE 7357352 8 = 8 ∧
      Apart 7357344 16 ((s.regs 4).toNat - 41512) (41512 + 112) := by
  obtain ⟨-, ⟨-, -, hw⟩, -, hd, -, -, -, -, hro, -⟩ := hce
  simp only [regSP] at hw
  obtain ⟨ha, h1, h2⟩ := stkTy_data hd
  have hA : Apart 7357344 16 ((s.regs 4).toNat - 41512) (41512 + 112) :=
    apart_of_data hd 4 (by decide) (by decide) hw
  have hR : Outside 7357344 16 R.rt := RoOut.out' hro 4 (by decide) (by decide)
  have hO : Outside 7357344 16 (R.rt ++ win s 41512 112) := by
    unfold Apart at hA
    simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨hR, by omega⟩
  refine ⟨by rw [hXF.accessible]; exact ha, ?_, ?_, hA⟩
  · rw [hXF.readLE _ _ (hO.of_sub (Nat.le_refl _) (by omega))]; exact h1
  · rw [hXF.readLE _ _ (hO.of_sub (by omega) (by omega))]; exact h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `newobject(type:big.stack)` precondition at its entry `X` (`RSP = sp - 240`) -/
theorem noPreM {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {s X : State} (hce : CallEnv R L s 41512 112)
    (hsv : RunIface.Serves R) (hXF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112))
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L X.mem)) (hb : 24 ≤ b)
    (hx4 : X.regs 4 = s.regs 4 - 240#64) (hx14 : X.regs 14 = s.regs 14) (hx0 : X.regs 0 = BitVec.ofNat 64 stkTy)
    (hXr : X.mem.readLE ((s.regs 4).toNat - 240) 8 = noR) :
    NewobjectPre64 4096 X ∧ StackRoom64 X 4096 1 ∧
      LiveAt R (cA "runtime.newobject") [(X.regs 0).toNat] L b (newobjectRound64 X) (X.regs 14).toNat X.mem
        (liveWin64 X 4096 1) := by
  obtain ⟨ta, t1, t2, hA⟩ := stkTy_at hce hXF
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  unfold Apart at hga hA
  have esp : (X.regs 4).toNat = (s.regs 4).toNat - 240 := sp240' hx4 hb'
  have eg : (X.regs 14).toNat = (s.regs 14).toNat := by rw [hx14]
  have e0 : (X.regs 0).toNat = 7357344 := by rw [hx0, stkTy_v]; rfl
  have hcs := cs_new esp hb'
  have hOw : ∀ a n, (s.regs 4).toNat + 112 ≤ a ∨ a + n ≤ (s.regs 4).toNat - 41512 → Outside a n R.rt →
      Outside a n (R.rt ++ win s 41512 112) := fun a n h1 h2 => by
    simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨h2, by omega⟩
  have hXa : ∀ a k w, X.mem.accessible a k w = s.mem.accessible a k w := hXF.accessible
  have hXg : X.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hXF.readLE _ _ (hOw _ _ (by omega) hgr)
  have hround : newobjectRound64 X = 24 := by
    simp only [newobjectRound64, typSize, typNoscan, typPtrBytes, e0, t1, t2]; decide
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hsv.2.2.2.2.1 _, ?_, ?_, ?_, ?_⟩
  · rw [esp, hXr]; decide
  · rw [esp]; omega
  · rw [esp]; omega
  · rw [esp]; omega
  · rw [esp, hXa]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [e0]; decide
  · rw [e0]; exact ta
  · simp only [typSize, e0, t1, maxAlloc]; omega
  · rw [hcs, e0]; simp only [outside_cons, outside_nil, and_true]; omega
  · rw [eg]; omega
  · rw [eg, hXa]; exact hg2
  · rw [eg, esp, hXg]; omega
  · rw [hcs, eg]; simp only [outside_cons, outside_nil, and_true]; omega
  · rw [eg]; exact hinv
  · rw [hround]; exact hb
  · intro r hr; have := hLs r hr
    simp only [liveWin64, hcs, esp, win, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro r hr
    simp only [liveWin64, hcs, esp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)

/-- what `newobject(type:big.stack)` gives (`p` the object; `M` = the memory at its entry) -/
structure NewNM (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M m : Janus.Arm64.Memory) (p : Nat) :
    Prop where
  mf : MemFrame M m (R.rt ++ [(sp - 240 - 4096, sp - 240), (sp - 232, sp - 224)])
  lf : LiveFrame M m L []
  rg : m.regions = M.regions
  rin : InRanges p 24 R.rt
  b48 : p + 24 ≤ 2 ^ 48
  acc : m.accessible p 24 true = true
  al : p % 8 = 0
  zero : ZeroBytes m p 24
  rap : ApartAll p 24 L
  cap : ApartAll p 24 [(sp - 240 - 4096, sp - 240), (sp - 232, sp - 224), (sp - 240, sp - 232)]
  inv : R.inv (b - 24) (L ++ [(p, p + 24)]) g (view R.rt (L ++ [(p, p + 24)]) m)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `newobject(type:big.stack)` call** at its entry `X` (continuation form) -/
theorem noCallM (impl : List Amd64.Segment) (R : RtInv)
    (hno : NewobjectLiveContract64 (LibDiv.program.link impl) (cA "runtime.newobject") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {s X : State} (hce : CallEnv R L s 41512 112)
    (hsv : RunIface.Serves R) (hXF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112))
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L X.mem)) (hb : 24 ≤ b)
    (hpc : X.rip = BitVec.ofNat 64 (cA "runtime.newobject"))
    (hx4 : X.regs 4 = s.regs 4 - 240#64) (hx14 : X.regs 14 = s.regs 14) (hx0 : X.regs 0 = BitVec.ofNat 64 stkTy)
    (hXr : X.mem.readLE ((s.regs 4).toNat - 240) 8 = noR) (ret0 : BitVec 64) (Q : State → Prop)
    (KC : ∀ (S' : State) (p : Nat), S'.rip = BitVec.ofNat 64 noR → S'.regs 4 = s.regs 4 - 232#64 →
      S'.regs 5 = X.regs 5 → S'.regs 14 = s.regs 14 → S'.fsBase = X.fsBase → S'.xmm 15 = X.xmm 15 →
      S'.df = X.df → S'.regs 0 = BitVec.ofNat 64 p → p < 2 ^ 64 →
      NewNM R b L (s.regs 14).toNat (s.regs 4).toNat X.mem S'.mem p →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 X Q := by
  have hb' : 41512 ≤ (s.regs 4).toNat := hce.2.1.1
  have esp : (X.regs 4).toNat = (s.regs 4).toNat - 240 := sp240' hx4 hb'
  have eg : (X.regs 14).toNat = (s.regs 14).toNat := by rw [hx14]
  have e0 : (X.regs 0).toNat = 7357344 := by rw [hx0, stkTy_v]; rfl
  obtain ⟨-, t1, t2, -⟩ := stkTy_at hce hXF
  have hsz : typSize X.mem (X.regs 0).toNat = 24 := by simp only [typSize, e0, t1]
  have hns : typNoscan X.mem (X.regs 0).toNat = false := by
    simp only [typNoscan, typPtrBytes, e0, t2]; decide
  have hround : newobjectRound64 X = 24 := by simp only [newobjectRound64, hsz, hns]; exact blockSize_stk24
  have hcs := cs_new esp hb'
  refine ReachesRet.call_regions (hno L b) hpc (noPreM hce hsv hXF hinv hb hx4 hx14 hx0 hXr)
    fun s1 hpc1 hpost hrg => ?_
  obtain ⟨ptr, junk, f, x, yh, m, zh, kr, hs1, hMF, hLF, hQ, hcap, hinv1⟩ := hpost
  rw [hsz] at hQ
  obtain ⟨hobj, hap⟩ := hQ (by omega)
  simp only [newobjectObj64, Fresh, hsz, hns, blockSize_stk24] at hobj
  obtain ⟨hin, h48, hacc, hal8, -, hz, -⟩ := hobj
  rw [hround] at hap hinv1 hcap
  rw [hcs] at hMF
  rw [liveWin64, hcs, esp] at hcap
  rw [eg] at hinv1
  subst hs1
  have hrg' : m.regions = X.mem.regions := hrg
  have hra : retAddrOf X = BitVec.ofNat 64 noR := by simp only [retAddrOf, esp, hXr]
  refine KC _ ptr.toNat (by simp only [retState64]; rw [hra]) (by simp only [retState64, callRegs64_apply, ↓reduceIte, hx4]; bv_omega)
    (by simp [retState64, callRegs64_apply]) (by simp [retState64, callRegs64_apply, hx14]) (by simp [retState64])
    (by simp [retState64]) (by simp [retState64]) (by simp [retState64, callRegs64_apply]) (BitVec.isLt _)
    ⟨hMF, hLF, hrg', hin, h48, hacc, hal8 (Or.inl (by decide)), hz trivial, hap, ?_, hinv1⟩
  rw [show (s.regs 4).toNat - 240 + 8 = (s.regs 4).toNat - 232 by omega] at hcap
  simpa only [List.cons_append, List.nil_append] using hcap

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem newStk_NM {R : RtInv} {L : List (Nat × Nat)} {b g sp : Nat} {M m M' : Janus.Arm64.Memory} {p : Nat}
    {ws : List (Nat × Nat)} (hNN : NewNM R b L g sp M m p) (hz : Outside 0 1 R.rt) (hb : 24 ≤ b)
    (hF : MemFrame m M' ws) (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) :
    NewStk R L (L ++ [(p, p + 24)]) b (b - 24) g M' p := by
  have ho := outside_of_rt hNN.rin hws
  have hp0 : 0 < p := by have := out_inR2 hz hNN.rin; omega
  have z0 : m.readLE p 8 = 0 := by have := hNN.zero.readLE (k := 0) (j := 8) (by omega); simpa using this
  have z8 : m.readLE (p + 8) 8 = 0 := hNN.zero.readLE (by omega)
  have z16 : m.readLE (p + 16) 8 = 0 := hNN.zero.readLE (by omega)
  have ew : stW M' p = 0 := by
    show M'.readLE p 8 = 0; rw [hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))]; exact z0
  have el : stLen M' p = 0 := by
    show M'.readLE (p + 8) 8 = 0; rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact z8
  have ec : stCap M' p = 0 := by
    show M'.readLE (p + 16) 8 = 0; rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact z16
  have hrE : stkRs M' p = [(p, p + 24)] := by simp only [stkRs, ec, ↓reduceIte]
  unfold NewStk
  rw [hrE, ew, el, ec]
  refine ⟨rfl, fun x hx => ?_, hp0, hNN.al, hNN.b48, by rw [hF.accessible]; exact hNN.acc, rfl, by decide,
    fun _ => rfl, by decide, by omega, fun h => absurd h (by decide), by unfold Apart; omega, by omega, by omega, ?_⟩
  · simp only [List.mem_singleton] at hx; subst hx
    simp only [Nat.add_sub_cancel_left]; exact ⟨hNN.rin, hNN.rap⟩
  · exact RtInv.inv_frame' hF (fun r hr => Or.inl (hws r hr)) hNN.inv

end FvModexp.Amd64.Q.NatDiv
