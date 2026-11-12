import FvModexp.Proofs.Arm64.Nat.DivMJoin

set_option autoImplicit false

/-!
# `nat.div` (arm64), `stk == nil`, the pool was empty: `newobject(type:big.stack)` (nat.go:289)

`noPreD` / `NewND` / `noCallD` / `newStk_ND`: agent expmc's `ExpN.noPreN` / `NewN` / `noCallN` (Arm64/Exp/NNilN.lean)
and `newStk_N` (NNilG.lean), adapted to `nat.div`'s frame (`SP' = sp - 240`, window `[sp - 41504, sp + 112)`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.DivNil

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

theorem stkTyD_v : stkTyD = 2764768 := rfl

theorem stkTyD_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE stkTyD 8 = 24 ∧ m.readLE (stkTyD + 8) 8 = 8 ∧ m.accessible stkTyD 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

theorem blockSize_stk : blockSize 24 false = 24 := by decide

set_option maxRecDepth 20000 in
/-- the `newobject(type:big.stack)` precondition from `SP' = sp - 240` -/
theorem noPreD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hKs : 41504 ≤ sp) (hsp2 : sp + 112 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - 41504) (41504 + 112) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 41504 < sp)
    (hwrt : Outside (sp - 41504) (41504 + 112) R.rt) (hgw : Apart (g + 16) 8 (sp - 41504) (41504 + 112))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - 41504, sp + 112)])
    (hd : Extracted.program.DataLoaded M) (hsv : RunIface.Serves R)
    (hinv : R.inv b L g (view R.rt L M)) (hb : 24 ≤ b)
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (sp - 240)) (h0 : S.regs 0 = BitVec.ofNat 64 stkTyD)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h30 : S.regs 30 = BitVec.ofNat 64 noRD) (hmem : S.mem = M) :
    NewobjectPre 4096 S ∧ StackRoom S 4096 1 ∧
      LiveAt R (cA "runtime.newobject") [(S.regs 0).toNat] L b (newobjectRound S) (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
  have esp : S.sp.toNat = sp - 240 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = stkTyD := by rw [h0, stkTyD_v]; rfl
  have e30 : (S.regs 30).toNat = noRD := by rw [h30, BitVec.toNat_ofNat]; decide
  obtain ⟨ht1, ht2, ht3⟩ := stkTyD_facts hd
  have hround : newobjectRound S = 24 := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, e0, hmem, ht1, ht2]; decide
  subst hmem
  unfold Apart at hgw
  have h := call_pre R L b (newobjectRound S) (cA "runtime.newobject") [(S.regs 0).toNat] (s := S) (S := S) (lo := sp - 41504)
    (hi := sp + 112) (stack := 4096) (nargs := 1) (fr := 0) (by rw [eg]; exact hg1) (by rw [eg]; exact hg2)
    (by rw [eg, esp]; omega) (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl
    (by omega) (by rw [esp]; omega) (by rw [e30]; decide) (by rw [e30]; decide) (by decide) (by omega) (by omega)
    (by omega) (by omega) (by rw [show sp + 112 - (sp - 41504) = 41504 + 112 by omega]; exact hwacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 112 - (sp - 41504) = 41504 + 112 by omega]; exact hwrt) hLs (hsv.2.2.2.2.1 _)
    (by rw [eg]; exact hinv) (by rw [hround]; exact hb)
  refine ⟨⟨h.1, ⟨by rw [e0, stkTyD_v]; decide, by rw [e0]; exact ht3⟩, ?_⟩, h.2.1, h.2.2⟩
  simp only [typSize, e0, ht1, maxAlloc]; omega

/-- what `newobject(type:big.stack)` gives (`p` the object) -/
structure NewND (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M m : Memory) (p : Nat) : Prop where
  mf : MemFrame M m (R.rt ++ [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)])
  lf : LiveFrame M m L []
  rg : m.regions = M.regions
  rin : InRanges p 24 R.rt
  b48 : p + 24 ≤ 2 ^ 48
  acc : m.accessible p 24 true = true
  al : p % 8 = 0
  zero : ZeroBytes m p 24
  rap : ApartAll p 24 L
  cap : ApartAll p 24 [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)]
  inv : R.inv (b - 24) (L ++ [(p, p + 24)]) g (view R.rt (L ++ [(p, p + 24)]) m)

set_option maxRecDepth 20000 in
/-- **the `newobject(type:big.stack)` call** (continuation form) -/
theorem noCallD (impl : List Segment) (R : RtInv) (hno : NewobjectLiveContract (LibDiv.program.link impl) (cA "runtime.newobject") 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hKs : 41504 ≤ sp) (hsp2 : sp + 112 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - 41504) (41504 + 112) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 41504 < sp)
    (hwrt : Outside (sp - 41504) (41504 + 112) R.rt) (hgw : Apart (g + 16) 8 (sp - 41504) (41504 + 112))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - 41504, sp + 112)])
    (hd : Extracted.program.DataLoaded M) (hsv : RunIface.Serves R)
    (hinv : R.inv b L g (view R.rt L M)) (hb : 24 ≤ b)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 (cA "runtime.newobject")) (hsp : S.sp = BitVec.ofNat 64 (sp - 240))
    (h0 : S.regs 0 = BitVec.ofNat 64 stkTyD) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h30 : S.regs 30 = BitVec.ofNat 64 noRD) (hmem : S.mem = M)
    (KC : ∀ (S' : State) (m : Memory) (p : Nat), S'.pc = BitVec.ofNat 64 noRD → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 p → p < 2 ^ 64 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.mem = m → NewND R b L g sp M m p →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 S Q := by
  have esp : S.sp.toNat = sp - 240 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = stkTyD := by rw [h0, stkTyD_v]; rfl
  obtain ⟨ht1, ht2, -⟩ := stkTyD_facts hd
  have hsz : typSize S.mem (S.regs 0).toNat = 24 := by simp only [typSize, e0, hmem, ht1]
  have hns : typNoscan S.mem (S.regs 0).toNat = false := by
    simp only [typNoscan, typPtrBytes, e0, hmem, ht2]; decide
  have hround : newobjectRound S = 24 := by
    simp only [newobjectRound, hsz, hns]; exact blockSize_stk
  have hcs : calleeStack S 4096 1 = [(sp - 240 - 4096, sp - 248), (sp - 232, sp - 224)] := by
    simp only [calleeStack, esp]
    rw [show sp - 240 - 8 = sp - 248 by omega, show sp - 240 + 8 = sp - 232 by omega,
      show sp - 232 + 8 * 1 = sp - 224 by omega]
  refine ReachesRet.call_regions (hno L b) hpc
    (noPreD R b L g sp M hal hKs hsp2 hwacc hg1 hg2 hg3 hwrt hgw hgrt hLs hd hsv hinv hb S hsp h0 h28 h30 hmem)
    fun s1 hpc1 hpost hrg => ?_
  obtain ⟨ptr, junk, f, v, m, ex, ep, hs1, hMF, hLF, hQ, hcap, hinv1⟩ := hpost
  rw [hsz] at hQ
  obtain ⟨hobj, hap⟩ := hQ (by omega)
  simp only [newobjectObj, Fresh, hsz, hns, blockSize_stk] at hobj
  obtain ⟨hin, h48, hacc, hal8, -, hz, -⟩ := hobj
  rw [hround] at hap hinv1 hcap
  rw [hcs, hmem] at hMF
  rw [hcs] at hcap
  rw [hmem] at hLF
  rw [eg] at hinv1
  subst hs1
  have hrg' : m.regions = M.regions := by rw [← hmem]; exact hrg
  refine KC _ m ptr.toNat (by simp only [retStateX]; exact h30) rfl ?_ (BitVec.isLt _)
    (by simp [retStateX, callRegs]) (by simp [retStateX, callRegs]) (by simp [retStateX, callRegs]) rfl
    ⟨hMF, hLF, hrg', hin, h48, hacc, hal8 (Or.inl (by decide)), hz trivial, hap, hcap, hinv1⟩
  simp [retStateX, callRegs]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem newStk_ND {R : RtInv} {L : List (Nat × Nat)} {b g sp : Nat} {M m M' : Memory} {p : Nat}
    {ws : List (Nat × Nat)} (hNN : NewND R b L g sp M m p) (hz : Outside 0 1 R.rt) (hb : 24 ≤ b)
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

end FvModexp.Arm64.NatDiv
