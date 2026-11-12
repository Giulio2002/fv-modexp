import FvModexp.Proofs.Arm64.Exp.NGet

/-!
# `nat.expNN` (arm64), `stk == nil`, the pool was empty: `Get`'s return fn+0x234 → `newobject(stack)` → rem | `J5`

nat.go:287-289 with `Get` = `nil` (`CMP R0, type:*big.stack` unequal ⇒ `R1 := 0`, `CBNZ R1` not taken):
* `getN`: fn+0x234 → `runtime.newobject` entry (`X0 = type:big.stack`, `X30` = fn+0x26c), memory unchanged;
* `noPreN` / `noCallN`: the live `newobject` call from `SP' = sp + 1056` (a zeroed 24-byte object `[p, p + 24)`,
  fresh wrt `L`, inside `R.rt`; budget `b - 24`; invariant for `L ++ [(p, p + 24)]`);
* `joinN`: fn+0x26c (`X0 = p`) → the defer record, the reloads and the join, as `NNilT.getT` (rem entry | `J5`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- `runtime.newobject` -/
abbrev noA : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- the type descriptor `type:big.stack` (`newobject`'s argument at fn+0x260) -/
abbrev stkTy : Nat := Extracted.dataAddr.«type:big.stack#c761f19c»

theorem stkTy_v : stkTy = 2764768 := rfl

/-- `newobject`'s return point (fn+0x26c) -/
abbrev noR : Nat := 1787164

theorem stkTy_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE stkTy 8 = 24 ∧ m.readLE (stkTy + 8) 8 = 8 ∧ m.accessible stkTy 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

theorem blockSize_stk : blockSize 24 false = 24 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- fn+0x234 with `Get` = nil → the `newobject` entry -/
theorem getN (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (sp : Nat) (M : Memory) (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 1048) 384 true = true)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 getR) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = 0#64) (h1 : S.regs 1 = 0#64) (hmem : S.mem = M)
    (KN : ∀ S' : State, S'.pc = BitVec.ofNat 64 noA → S'.sp = S.sp → S'.regs 0 = BitVec.ofNat 64 stkTy →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      S'.regs 30 = BitVec.ofNat 64 noR → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  janus_run [] until [noA]
  refine KN _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | rfl

set_option maxRecDepth 20000 in
/-- the `newobject(type:big.stack)` precondition from `SP' = sp + 1056` -/
theorem noPreN (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hK : 4304 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 1432) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 1432) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 1432))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hd : Extracted.program.DataLoaded M) (hsv : RunIface.Serves R)
    (hinv : R.inv b L g (view R.rt L M)) (hb : 24 ≤ b)
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h0 : S.regs 0 = BitVec.ofNat 64 stkTy)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h30 : S.regs 30 = BitVec.ofNat 64 noR) (hmem : S.mem = M) :
    NewobjectPre 4096 S ∧ StackRoom S 4096 1 ∧
      LiveAt R noA [(S.regs 0).toNat] L b (newobjectRound S) (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
  have esp : S.sp.toNat = sp + 1056 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = stkTy := by rw [h0, stkTy_v]; rfl
  have e30 : (S.regs 30).toNat = noR := by rw [h30, BitVec.toNat_ofNat]; decide
  obtain ⟨ht1, ht2, ht3⟩ := stkTy_facts hd
  have hround : newobjectRound S = 24 := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, e0, hmem, ht1, ht2]; decide
  subst hmem
  unfold Apart at hgw
  have h := call_pre R L b (newobjectRound S) noA [(S.regs 0).toNat] (s := S) (S := S) (lo := sp - K)
    (hi := sp + 1432) (stack := 4096) (nargs := 1) (fr := 0) (by rw [eg]; exact hg1) (by rw [eg]; exact hg2)
    (by rw [eg, esp]; omega) (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl
    (by omega) (by rw [esp]; omega) (by rw [e30]; decide) (by rw [e30]; decide) (by decide) (by omega) (by omega)
    (by omega) (by omega) (by rw [show sp + 1432 - (sp - K) = K + 1432 by omega]; exact hwacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 1432 - (sp - K) = K + 1432 by omega]; exact hwrt) hLs (hsv.2.2.2.2.1 _)
    (by rw [eg]; exact hinv) (by rw [hround]; exact hb)
  refine ⟨⟨h.1, ⟨by rw [e0, stkTy_v]; decide, by rw [e0]; exact ht3⟩, ?_, ?_⟩, h.2.1, h.2.2⟩
  · simp only [typSize, e0, ht1, maxAlloc]; omega
  · rw [e0]
    exact outside_calleeStack_of_data hd (by decide +kernel) (by rw [esp]; omega)
      (by rw [esp]; exact Memory.accessible_mono _ hwacc (by omega) (by omega))

/-- what `newobject(type:big.stack)` gives (`p` the object) -/
structure NewN (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M m : Memory) (p : Nat) : Prop where
  mf : MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)])
  lf : LiveFrame M m L []
  rg : m.regions = M.regions
  rin : InRanges p 24 R.rt
  b48 : p + 24 ≤ 2 ^ 48
  acc : m.accessible p 24 true = true
  al : p % 8 = 0
  zero : ZeroBytes m p 24
  rap : ApartAll p 24 L
  cap : ApartAll p 24 [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)]
  inv : R.inv (b - 24) (L ++ [(p, p + 24)]) g (view R.rt (L ++ [(p, p + 24)]) m)

set_option maxRecDepth 20000 in
/-- **the `newobject(type:big.stack)` call** (continuation form) -/
theorem noCallN (impl : List Segment) (R : RtInv) (hno : NewobjectLiveContract (LibN.program.link impl) noA 4096 R)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hK : 4304 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 1432) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 1432) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 1432))
    (hgrt : Outside (g + 16) 8 R.rt) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hd : Extracted.program.DataLoaded M) (hsv : RunIface.Serves R)
    (hinv : R.inv b L g (view R.rt L M)) (hb : 24 ≤ b)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 noA) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h0 : S.regs 0 = BitVec.ofNat 64 stkTy) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h30 : S.regs 30 = BitVec.ofNat 64 noR) (hmem : S.mem = M)
    (KC : ∀ (S' : State) (m : Memory) (p : Nat), S'.pc = BitVec.ofNat 64 noR → S'.sp = S.sp →
      S'.regs 0 = BitVec.ofNat 64 p → p < 2 ^ 64 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.mem = m → NewN R b L g sp M m p →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have esp : S.sp.toNat = sp + 1056 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have e0 : (S.regs 0).toNat = stkTy := by rw [h0, stkTy_v]; rfl
  obtain ⟨ht1, ht2, -⟩ := stkTy_facts hd
  have hsz : typSize S.mem (S.regs 0).toNat = 24 := by simp only [typSize, e0, hmem, ht1]
  have hns : typNoscan S.mem (S.regs 0).toNat = false := by
    simp only [typNoscan, typPtrBytes, e0, hmem, ht2]; decide
  have hround : newobjectRound S = 24 := by
    simp only [newobjectRound, hsz, hns]; exact blockSize_stk
  have hcs : calleeStack S 4096 1 = [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)] := by
    simp only [calleeStack, esp]
    rw [show sp + 1056 - 8 = sp + 1048 by omega, show sp + 1056 + 8 = sp + 1064 by omega]
  refine Reaches.call_regions (Summary.withExit (hno L b) hret) hpc
    (noPreN R b L K g sp M hal hK hKs hsp2 hwacc hg1 hg2 hg3 hwrt hgw hgrt hLs hd hsv hinv hb S hsp h0 h28 h30 hmem)
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

end FvModexp.Arm64.ExpN
