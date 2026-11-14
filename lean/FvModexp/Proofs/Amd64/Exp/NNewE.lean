import FvModexp.Proofs.Amd64.Exp.NGetE
import FvModexp.Proofs.Amd64.Nat.StkTyData
import FvModexp.Proofs.Amd64.Nat.DivMStk

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`, the pool was empty: `newobject(type:big.stack)` (nat.go:289) (agent expmc s74;
twin of `Arm64.ExpN.getN` / `noCall`, adapted from top's Amd64/NatQ/DivMNew.lean `noPreM` / `noCallM`)

* `getNE`: `Get` returned nil (`RAX = RBX = 0`): `CMPQ AX, CX` (not `type:*big.stack`) → `XORL BX`, `TESTQ BX` → `LEAQ
  type:big.stack, AX`, `CALL runtime.newobject` (return `noR` pushed at `t - 0x110`).
* `noCallE`: the call at its entry (`RSP = sp + 0x388 = t - 0x110`), result in top's `NewNM` form at `sp + 0x478`
  (`NewNM`'s callee window `[sp' - 240 - 4096, sp' - 240) ∪ [sp' - 232, sp' - 224)` = `[t - 0x110 - 4096, t - 0x110) ∪
  [t - 0x108, t - 0x100)`); the descriptor facts (`StkTyData.stkTy_data`, `apart_of_data`, `RoOut`) are premises.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

set_option linter.janusRenameI false

namespace FvModexp.Amd64.ExpN

theorem blockSize_stk24 : blockSize 24 false = 24 := by decide

/-! `NewNM` / `newStk_NM`: copied unchanged from top's Amd64/NatQ/DivMNew.lean (adapted from fv-modexp
Amd64/NatQ/DivMNew.lean), so that this chain does not import `nat.div`'s. -/

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `Get` returned nil: to `newobject(type:big.stack)`'s entry -/
theorem getNE (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t : Nat) (M : Janus.Arm64.Memory) (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 0x110) 8 true = true)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 getR) (hS4 : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h0 : S.regs 0 = 0#64) (h3 : S.regs 3 = 0#64) (hmem : S.mem = M)
    (KN : ∀ (X : State), X.rip = BitVec.ofNat 64 (cA "runtime.newobject") →
      X.regs 4 = BitVec.ofNat 64 (t - 0x110) → X.regs 0 = BitVec.ofNat 64 stkTy →
      X.regs 5 = S.regs 5 → X.regs 14 = S.regs 14 → X.fsBase = S.fsBase → X.df = S.df →
      X.xmm 15 = S.xmm 15 → X.mem = M.writeLE (t - 0x110) 8 noR →
      Reaches ((LibNE.program.link impl).withExit ret0) X Q) :
    Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  subst hmem
  janus64_run [es1, h0, h3] until [cA "runtime.newobject"]
  refine KN _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (janus64_simp; done)
    | (simp only [Janus.Arm64.Memory.writeLE]; done)
    | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `newobject(type:big.stack)` call** at its entry `X` (`RSP = sp + 0x388`), in continuation form -/
theorem noCallE (impl : List Amd64.Segment) (R : RtInv)
    (hno : NewobjectLiveContract64 (LibNE.program.link impl) (cA "runtime.newobject") 4096 R)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (Q : Amd64.Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Janus.Arm64.Memory)
    (hal : sp % 8 = 0) (hK : 41640 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 0x510 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 0x510) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 0x510) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 0x510))
    (hLs : LiveSep L [(sp - K, sp + 0x510)]) (hsv : RunIface.Serves R)
    (hinv : R.inv b L g (view R.rt L M)) (hb : 24 ≤ b)
    (ta : M.accessible 7357344 16 false = true) (t1 : M.readLE 7357344 8 = 24) (t2 : M.readLE 7357352 8 = 8)
    (hA : Apart 7357344 16 (sp - K) (K + 0x510))
    (X : State) (hpc : X.rip = BitVec.ofNat 64 (cA "runtime.newobject"))
    (hx4 : X.regs 4 = BitVec.ofNat 64 (sp + 0x388)) (hx14 : X.regs 14 = BitVec.ofNat 64 g)
    (hx0 : X.regs 0 = BitVec.ofNat 64 stkTy) (hmem : X.mem = M) (hXr : M.readLE (sp + 0x388) 8 = noR)
    (KC : ∀ (S' : State) (p : Nat), S'.rip = BitVec.ofNat 64 noR → S'.regs 4 = BitVec.ofNat 64 (sp + 0x390) →
      S'.regs 5 = X.regs 5 → S'.regs 14 = X.regs 14 → S'.fsBase = X.fsBase → S'.xmm 15 = X.xmm 15 →
      S'.df = X.df → S'.regs 0 = BitVec.ofNat 64 p → p < 2 ^ 64 →
      NewNM R b L g (sp + 0x478) M S'.mem p →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibNE.program.link impl).withExit ret0) X Q := by
  unfold Apart at hgw hA
  have esp : (X.regs 4).toNat = sp + 0x388 := by rw [hx4, BitVec.toNat_ofNat]; omega
  have eg : (X.regs 14).toNat = g := by rw [hx14, BitVec.toNat_ofNat]; omega
  have e0 : (X.regs 0).toNat = 7357344 := by rw [hx0, stkTy_v]; rfl
  have hcs : calleeStack64 X 4096 1 = [(sp + 0x478 - 240 - 4096, sp + 0x478 - 240),
      (sp + 0x478 - 232, sp + 0x478 - 224)] := by
    simp only [calleeStack64, esp]
    rw [show sp + 0x478 - 240 = sp + 0x388 by omega, show sp + 0x478 - 232 = sp + 0x390 by omega,
      show sp + 0x478 - 224 = sp + 0x388 + 8 + 8 * 1 by omega]
  subst hmem
  have hsz : typSize X.mem (X.regs 0).toNat = 24 := by simp only [typSize, e0, t1]
  have hns : typNoscan X.mem (X.regs 0).toNat = false := by
    simp only [typNoscan, typPtrBytes, e0, t2]; decide
  have hround : newobjectRound64 X = 24 := by simp only [newobjectRound64, hsz, hns]; exact blockSize_stk24
  have hpre : NewobjectPre64 4096 X ∧ StackRoom64 X 4096 1 ∧
      LiveAt R (cA "runtime.newobject") [(X.regs 0).toNat] L b (newobjectRound64 X) (X.regs 14).toNat X.mem
        (liveWin64 X 4096 1) := by
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hsv.2.2.2.2.1 _, ?_, ?_, ?_, ?_⟩
    · rw [esp, hXr]; decide
    · rw [esp]; omega
    · rw [esp]; omega
    · rw [esp]; omega
    · rw [esp]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
    · rw [e0]; decide
    · rw [e0]; exact ta
    · simp only [typSize, e0, t1, maxAlloc]; omega
    · rw [hcs, e0]; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [eg]; omega
    · rw [eg]; exact hg2
    · rw [eg, esp]; omega
    · rw [hcs, eg]; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [eg]; exact hinv
    · rw [hround]; exact hb
    · intro r hr; have := hLs r hr
      simp only [liveWin64, hcs, esp, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true] at this ⊢
      omega
    · intro r hr
      simp only [liveWin64, hcs, esp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hwrt.of_sub (by simp only; omega) (by simp only; omega)
  refine Reaches.call_regions ((hno L b).withExit hret) hpc hpre fun s1 hpc1 hpost hrg => ?_
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
    (by simp [retState64, callRegs64_apply]) (by simp [retState64, callRegs64_apply]) (by simp [retState64])
    (by simp [retState64]) (by simp [retState64]) (by simp [retState64, callRegs64_apply]) (BitVec.isLt _)
    ⟨hMF, hLF, hrg', hin, h48, hacc, hal8 (Or.inl (by decide)), hz trivial, hap, ?_, hinv1⟩
  rw [show sp + 0x388 + 8 = sp + 0x478 - 232 by omega, show sp + 0x388 = sp + 0x478 - 240 by omega] at hcap
  simpa only [List.cons_append, List.nil_append] using hcap

end FvModexp.Amd64.ExpN
