import FvModexp.Proofs.Arm64.Exp.P2W2WC
import FvModexp.Proofs.Arm64.Nat.StackNatCall

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `WC` through a live allocation (`makeslice` / `newobject`) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a range of the window strictly below the saved FP is outside `WN` -/
theorem cs_out {a k : Nat} {cs : List (Nat × Nat)} (hcs : ∀ q ∈ cs, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456)
    (ho : Outside a k (WN sp K)) : Outside a k cs := by
  simp only [WN, outside_cons, outside_nil, and_true] at ho
  refine outside_of_forall fun q hq => ?_
  have := hcs q hq; omega

/-- the stack header through a step that writes only the runtime's ranges and `cs` (in the window) and keeps `L1` -/
theorem hdr_keep (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456) (hLF : LiveFrame M m L1 []) {a k : Nat} (h1 : st ≤ a)
    (h2 : a + k ≤ st + 24) : m.readLE a k = M.readLE a k := by
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  rcases h.sok.2.1 with hL | hO
  · exact hLF.readLE a k (hL.sub h1 h2) trivial
  · refine hMF.readLE a k ?_
    rw [outside_append]
    refine ⟨hO.of_sub h1 h2, outside_of_forall fun q hq => ?_⟩
    have := hcs q hq; omega

/-- **`WC` through a live allocation** of `[p, p + r)` -/
theorem WC.alloc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456) (hLF : LiveFrame M m L1 []) (hrg : m.regions = M.regions)
    {p r : Nat} (hin : InRanges p r R.rt) (hap : ApartAll p r L1)
    (hinv : R.inv (b1 - r) (L1 ++ [(p, p + r)]) g (view R.rt (L1 ++ [(p, p + r)]) m)) :
    WC R L K g sp st zp zc s.mem m (L1 ++ [(p, p + r)]) (b1 - r) ℓ := by
  have e0 : stW m st = stW M st := hdr_keep hP h hMF hcs hLF (Nat.le_refl _) (by omega)
  have e1 : stLen m st = stLen M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have e2 : stCap m st = stCap M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + r)]) :=
    LiveExt.single (by rw [show p + r - p = r by omega]; exact hin) (by rw [show p + r - p = r by omega]; exact hap)
  refine h.call hMF hLF hrg (fun a k _ o2 _ _ => cs_out hcs o2) (fun _ _ _ _ => trivial) hx hinv
    (stkOK_hdr h.sok hMF e0 e1 e2 hx) (e1.trans h.len) (Nat.le_refl _) (Or.inl ⟨e0, e2⟩)
    (fun hn => absurd ⟨e0, e2⟩ hn)

/-- the `[1]Word` type descriptor (`newobject`'s argument at `0x1b66b0`) -/
abbrev a1T : Nat := 2671872

theorem a1T_facts {m : Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE a1T 8 = 8 ∧ m.readLE (a1T + 8) 8 = 0 ∧ m.accessible a1T 16 false = true :=
  ⟨Janus.Tactic.readLE_of_dataRead hd (by decide +kernel), Janus.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Tactic.accessible_of_dataRead hd (by decide +kernel)⟩

set_option maxRecDepth 20000 in
/-- the facts every live-contract call at `SP = sp` needs (`call_pre` with `s := S`) -/
theorem wcall (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (S : State) (hsp : S.sp = BitVec.ofNat 64 sp) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hm : S.mem = M)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48) (nargs : Nat) (hn : nargs ≤ 5)
    (addr : Nat) (args : List Nat) (hok : R.ok addr args) (cost : Nat) (hcost : cost ≤ b1) :
    CallOK S 4096 nargs ∧ StackRoom S 4096 nargs ∧
      LiveAt R addr args L1 b1 cost (S.regs 28).toNat S.mem (calleeStack S 4096 nargs) := by
  have hce := h.cenv hP
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, -, -⟩ := hce
  have hK0 : 4304 ≤ K := hP.1.2.2.2.2.2.2.2.1
  have esp : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have eg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  subst hm
  unfold Apart at hga
  refine call_pre R L1 b1 cost addr args (s := S) (S := S) (lo := sp - K) (hi := sp + 88) (stack := 4096)
    (nargs := nargs) (fr := 0) (by rw [eg]; exact hg1) (by rw [eg]; exact hg2) (by rw [eg, esp]; omega)
    (by rw [eg]; simp only [outside_cons]; exact ⟨by omega, hgrt⟩) (MemFrame.refl _ _) rfl (by omega)
    (by rw [esp]; exact hal) h30a h30b (by decide) (by omega) (by omega) (by omega) (by omega)
    (by rw [show sp + 88 - (sp - K) = K + 88 by omega]; exact hacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 88 - (sp - K) = K + 88 by omega]; exact hrt) hLs hok (by rw [eg]; exact h.inv) hcost

set_option maxRecDepth 20000 in
/-- the pre of `makeslice(Word, n, c)` at a call from `SP = sp` -/
theorem mkPre (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {mk : Nat} (hmk : Extracted.program.contractAddr "runtime.makeslice" = mk)
    (T : State) (hsp : T.sp = BitVec.ofNat 64 sp) (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M)
    (h0 : T.regs 0 = 2641088#64) {n c : Nat} (h1 : T.regs 1 = BitVec.ofNat 64 n)
    (h2 : T.regs 2 = BitVec.ofNat 64 c) (h30a : (T.regs 30).toNat % 4 = 0) (h30b : (T.regs 30).toNat < 2 ^ 48)
    (hnc : n ≤ c) (hc : c ≤ 2 ^ 17) (hcost : blockSize (8 * c) true ≤ b1) :
    MakeslicePre 4096 T ∧ StackRoom T 4096 3 ∧
      LiveAt R mk [(T.regs 0).toNat, (T.regs 1).toNat, (T.regs 2).toNat] L1 b1 (makesliceRound T)
        (T.regs 28).toNat T.mem (calleeStack T 4096 3) := by
  have hd : Extracted.program.DataLoaded M := (h.cenv hP).2.2.2.2.2.2.2.2.2.2.2.1
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts hd
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3
  have t0 : (T.regs 0).toNat = 2641088 := by rw [h0]; rfl
  have t1 : (T.regs 1).toNat = n := by rw [h1, BitVec.toNat_ofNat]; omega
  have t2 : (T.regs 2).toNat = c := by rw [h2, BitVec.toNat_ofNat]; omega
  have hround : makesliceRound T = blockSize (8 * c) true := by
    simp only [makesliceRound, typSize, typNoscan, typPtrBytes, t0, t2, hm, ht1, ht2]; rfl
  have hc := wcall hP h T hsp h28 hm h30a h30b 3 (by omega) mk [(T.regs 0).toNat, (T.regs 1).toNat, (T.regs 2).toNat]
    (by rw [← hmk, t0, t1, t2]; exact hsv.1 _ _ _ hc) (makesliceRound T) (by rw [hround]; exact hcost)
  refine ⟨⟨hc.1, ⟨by omega, by rw [t0, hm]; exact ht3⟩, by omega, by omega, ?_⟩, hc.2⟩
  simp only [typSize, t0, t2, hm, ht1, maxAlloc]; omega

set_option maxRecDepth 20000 in
/-- the pre of `newobject([1]Word)` at a call from `SP = sp` -/
theorem noPre (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {no : Nat} (hno : Extracted.program.contractAddr "runtime.newobject" = no)
    (T : State) (hsp : T.sp = BitVec.ofNat 64 sp) (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M)
    (h0 : T.regs 0 = 2671872#64) (h30a : (T.regs 30).toNat % 4 = 0) (h30b : (T.regs 30).toNat < 2 ^ 48)
    (hcost : blockSize 8 true ≤ b1) :
    NewobjectPre 4096 T ∧ StackRoom T 4096 1 ∧
      LiveAt R no [(T.regs 0).toNat] L1 b1 (newobjectRound T) (T.regs 28).toNat T.mem (calleeStack T 4096 1) := by
  have hd : Extracted.program.DataLoaded M := (h.cenv hP).2.2.2.2.2.2.2.2.2.2.2.1
  have hsv : RunIface.Serves R := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ht1, ht2, ht3⟩ := a1T_facts hd
  have hwTv : a1T = 2671872 := rfl
  rw [hwTv] at ht1 ht2 ht3
  have t0 : (T.regs 0).toNat = 2671872 := by rw [h0]; rfl
  have hround : newobjectRound T = blockSize 8 true := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, t0, hm, ht1, ht2]; rfl
  have hc := wcall hP h T hsp h28 hm h30a h30b 1 (by omega) no [(T.regs 0).toNat]
    (by rw [← hno]; exact hsv.2.2.2.2.1 _) (newobjectRound T) (by rw [hround]; exact hcost)
  refine ⟨⟨hc.1, ⟨by omega, by rw [t0, hm]; exact ht3⟩, ?_⟩, hc.2⟩
  simp only [typSize, t0, hm, ht1, maxAlloc]; omega

/-- the facts after a live allocation of `[p, p + r)` (`n` bytes asked) at a call from `SP = sp`, memory `M → m` -/
structure AllocR (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory) (L1 : List (Nat × Nat))
    (b1 ℓ : Nat) (m : Memory) (p r n : Nat) : Prop where
  wc : WC R L K g sp st zp zc m0 m (L1 ++ [(p, p + r)]) (b1 - r) ℓ
  rin : InRanges p r R.rt
  rap : ApartAll p r L1
  b48 : p + r ≤ 2 ^ 48
  acc : m.accessible p r true = true
  al : p % 8 = 0
  sz : n ≤ r
  rc : r ≤ allocCost n
  keep : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 32 ≤ a ∧ a + k ≤ sp + 560) → m.readLE a k = M.readLE a k

set_option maxRecDepth 20000 in
/-- `makeslice(Word, _, c)`'s post as `AllocR` -/
theorem mkPost (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (T : State) (hsp : T.sp = BitVec.ofNat 64 sp) (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M)
    (h0 : T.regs 0 = 2641088#64) {c : Nat}
    (h2 : T.regs 2 = BitVec.ofNat 64 c) (hc0 : 0 < c) (hc : c ≤ 2 ^ 17) (S1 : State)
    (hrg : S1.mem.regions = T.mem.regions)
    (hpost : LiveAllocRet R 4096 3 (fun ptr => [ptr]) L1 b1 (makesliceRound T) (makesliceRound T) T S1
      fun m ptr => 0 < typSize T.mem (T.regs 0).toNat * (T.regs 2).toNat →
        makesliceObj R.rt T m ptr ∧ ApartAll ptr (makesliceRound T) L1) :
    ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
      (ep : Nat → Bool), S1 = retStateX T junk [ptr] f v m ex ep ∧
        AllocR R L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize (8 * c) true) (8 * c) := by
  have hd : Extracted.program.DataLoaded M := (h.cenv hP).2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ht1, ht2, -⟩ := StackNat.wT_facts hd
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hg24 := hP.1.2.2.1
  have t0 : (T.regs 0).toNat = 2641088 := by rw [h0]; rfl
  have t2 : (T.regs 2).toNat = c := by rw [h2, BitVec.toNat_ofNat]; omega
  have esp : T.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hsz : typSize T.mem (T.regs 0).toNat * (T.regs 2).toNat = 8 * c := by
    simp only [typSize, t0, t2, hm, ht1]
  have hround : makesliceRound T = blockSize (8 * c) true := by
    simp only [makesliceRound, typSize, typNoscan, typPtrBytes, t0, t2, hm, ht1, ht2]; rfl
  obtain ⟨ptr, junk, f, v, m, ex, ep, hs1, hMF, hLF, hQ, -, hinv⟩ := hpost
  rw [hsz] at hQ
  obtain ⟨hobj, hap⟩ := hQ (by omega)
  simp only [makesliceObj, Fresh, hsz] at hobj
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, hm, ht2]; rfl
  rw [hround] at hap hinv
  rw [hns] at hobj
  obtain ⟨hin, h48, hacc, hal, -, -, hle⟩ := hobj
  have hcs : ∀ q ∈ calleeStack T 4096 3, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456 := by
    intro q hq; simp only [calleeStack, esp, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  rw [hm] at hMF hLF
  have hgg : (T.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  rw [hgg] at hinv
  refine ⟨ptr, junk, f, v, m, ex, ep, hs1, h.alloc hP hMF hcs hLF ?rg hin hap hinv, hin, hap, h48, hacc,
    hal (Or.inr (by omega)), hle, blockSize_le_allocCost _ _, fun a k ha => hMF.readLE a k ?_⟩
  case rg => subst hs1; rw [← hm]; exact hrg
  · rw [outside_append]
    refine ⟨?_, ?_⟩
    · have := hP.win_rt
      exact this.of_sub (by omega) (by omega)
    · simp only [calleeStack, esp, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- `newobject([1]Word)`'s post as `AllocR` -/
theorem noPost (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    (T : State) (hsp : T.sp = BitVec.ofNat 64 sp) (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M)
    (h0 : T.regs 0 = 2671872#64) (S1 : State)
    (hrg : S1.mem.regions = T.mem.regions)
    (hpost : LiveAllocRet R 4096 1 (fun ptr => [ptr]) L1 b1 (newobjectRound T) (newobjectRound T) T S1
      fun m ptr => 0 < typSize T.mem (T.regs 0).toNat →
        newobjectObj R.rt T m ptr ∧ ApartAll ptr (newobjectRound T) L1) :
    ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
      (ep : Nat → Bool), S1 = retStateX T junk [ptr] f v m ex ep ∧
        AllocR R L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize 8 true) 8 := by
  have hd : Extracted.program.DataLoaded M := (h.cenv hP).2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ht1, ht2, -⟩ := a1T_facts hd
  have hwTv : a1T = 2671872 := rfl
  rw [hwTv] at ht1 ht2
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hg24 := hP.1.2.2.1
  have t0 : (T.regs 0).toNat = 2671872 := by rw [h0]; rfl
  have esp : T.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hsz : typSize T.mem (T.regs 0).toNat = 8 := by
    simp only [typSize, t0, hm, ht1]
  have hround : newobjectRound T = blockSize 8 true := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, t0, hm, ht1, ht2]; rfl
  obtain ⟨ptr, junk, f, v, m, ex, ep, hs1, hMF, hLF, hQ, -, hinv⟩ := hpost
  rw [hsz] at hQ
  obtain ⟨hobj, hap⟩ := hQ (by omega)
  simp only [newobjectObj, Fresh, hsz] at hobj
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, hm, ht2]; rfl
  rw [hround] at hap hinv
  rw [hns] at hobj
  obtain ⟨hin, h48, hacc, hal, -, -, hle⟩ := hobj
  have hcs : ∀ q ∈ calleeStack T 4096 1, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456 := by
    intro q hq; simp only [calleeStack, esp, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  rw [hm] at hMF hLF
  have hgg : (T.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  rw [hgg] at hinv
  refine ⟨ptr, junk, f, v, m, ex, ep, hs1, h.alloc hP hMF hcs hLF ?rg hin hap hinv, hin, hap, h48, hacc,
    hal (Or.inr (by decide)), hle, blockSize_le_allocCost _ _, fun a k ha => hMF.readLE a k ?_⟩
  case rg => subst hs1; rw [← hm]; exact hrg
  · rw [outside_append]
    refine ⟨?_, ?_⟩
    · have := hP.win_rt
      exact this.of_sub (by omega) (by omega)
    · simp only [calleeStack, esp, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- `[p] = 1` into a fresh one-word object: `WC`, the slots and the result `nat{1}` -/
theorem fresh1 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {m : Memory} {p r : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem M L1 b1 ℓ m p r 8) (hle : LiveExt R L L1) {r29 : BitVec 64} {ret : Nat}
    (hsl : ESl M sp st r29 ret zp zc xp xl xc yp yl lm (stLen s.mem st)) :
    WC R L K g sp st zp zc s.mem (m.writeLE p 8 1) (L1 ++ [(p, p + r)]) (b1 - r) ℓ ∧
      ESl (m.writeLE p 8 1) sp st r29 ret zp zc xp xl xc yp yl lm (stLen s.mem st) ∧
      ExpHyp.NatOF R L (L1 ++ [(p, p + r)]) (m.writeLE p 8 1) zp zc 1 p 1 1 1 := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpw := hA.rin.apart hout
  have hsz := hA.sz
  unfold Apart at hpw hstw
  have hF1 : MemFrame m (m.writeLE p 8 1) [(p, p + 8)] :=
    (MemFrame.refl _ _).writeLE_inRanges _ ⟨(p, p + 8), by simp, by simp only; omega, by simp only; omega⟩
  have hin2 : InRanges p 8 (L1 ++ [(p, p + r)]) :=
    ⟨(p, p + r), by simp, by simp only; omega, by simp only; omega⟩
  have hapL : ApartAll p r L := fun q hq => hA.rap q (hle.mem_old hq)
  have hsok0 := hP.stk0
  have hhdA : Apart p r st 24 := by
    rcases hsok0.2.1 with hL0 | hO0
    · have := hapL.apart_of_inRanges hL0; unfold Apart; omega
    · exact (hA.rin.apart hO0).symm
  unfold Apart at hhdA
  have hws : InRanges p 8 R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  refine ⟨hA.wc.frame hF1 (by simp only [Memory.regions_writeLE]) (fun a k ho => ?_) (fun a k hin _ => ?_) ?_ ?_,
    ESl.keep hsl (fun a k ha => by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hA.keep a k (by omega)) (by omega), ?_⟩
  · rw [outside_append, outside_append] at ho
    have := hA.rin.apart ho.1.1
    unfold Apart at this
    simp only [outside_cons, outside_nil, and_true]; omega
  · have := hapL.apart_of_inRanges hin
    simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega
  · intro q hq; simp only [List.mem_singleton] at hq; subst hq; simp only
    rw [show p + 8 - p = 8 by omega]; exact Or.inl hin2
  · refine ⟨?_, Or.inr ?_, Nat.le_refl _, by decide, fun _ => ⟨hA.al, Or.inl hin2, ?_, by have := hA.b48; omega⟩,
      Or.inr ⟨Nat.le_refl _, hws, fun q hq => ?_⟩⟩
    · show (m.writeLE p 8 1).readLE p (8 * 1) = 1
      rw [Memory.readLE_writeLE_self]
    · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Memory.readLE_writeLE_self]; decide
    · simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega)
    · have := hapL q hq; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- **`makeslice(Word, n, c)` from `SP = sp`** (continuation form; the return state is `retStateX T …`) -/
theorem mkCall {impl : List Segment} {mk : Nat} (hmkE : Extracted.program.contractAddr "runtime.makeslice" = mk)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) mk 4096 R) (ret0 : BitVec 64) (Q : State → Prop)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {n c ra : Nat} (hnc : n ≤ c) (hc0 : 0 < c) (hc : c ≤ 2 ^ 17) (hra4 : ra % 4 = 0) (hra : ra < 2 ^ 48)
    (hcost : blockSize (8 * c) true ≤ b1)
    (KC : ∀ (T : State) (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
      (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      AllocR R L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize (8 * c) true) (8 * c) →
      ReachesRet (LibExp.program.link impl) ret0 (retStateX T junk [ptr] f v m ex ep) Q)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mk) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M) (h0 : T.regs 0 = 2641088#64)
    (h1 : T.regs 1 = BitVec.ofNat 64 n) (h2 : T.regs 2 = BitVec.ofNat 64 c) (h30 : T.regs 30 = BitVec.ofNat 64 ra) :
    ReachesRet (LibExp.program.link impl) ret0 T Q := by
  have e30 : (T.regs 30).toNat = ra := by rw [h30, BitVec.toNat_ofNat]; omega
  refine ReachesRet.call_regions (hmk L1 b1) hpc
    (mkPre hP h hmkE T hsp h28 hm h0 h1 h2 (by rw [e30]; exact hra4) (by rw [e30]; exact hra) hnc hc hcost) ?_
  intro S1 _ hpost hrg1
  obtain ⟨ptr, junk, f, v, m, ex, ep, rfl, hA⟩ := mkPost hP h T hsp h28 hm h0 h2 hc0 hc S1 hrg1 hpost
  exact KC T ptr junk f v m ex ep hA

set_option maxRecDepth 20000 in
/-- **`newobject([1]Word)` from `SP = sp`** (continuation form) -/
theorem noCall {impl : List Segment} {no : Nat} (hnoE : Extracted.program.contractAddr "runtime.newobject" = no)
    (hno : NewobjectLiveContract (LibExp.program.link impl) no 4096 R) (ret0 : BitVec 64) (Q : State → Prop)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {ra : Nat} (hra4 : ra % 4 = 0) (hra : ra < 2 ^ 48) (hcost : blockSize 8 true ≤ b1)
    (KC : ∀ (T : State) (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
      (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      AllocR R L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize 8 true) 8 →
      ReachesRet (LibExp.program.link impl) ret0 (retStateX T junk [ptr] f v m ex ep) Q)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 no) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M) (h0 : T.regs 0 = 2671872#64)
    (h30 : T.regs 30 = BitVec.ofNat 64 ra) :
    ReachesRet (LibExp.program.link impl) ret0 T Q := by
  have e30 : (T.regs 30).toNat = ra := by rw [h30, BitVec.toNat_ofNat]; omega
  refine ReachesRet.call_regions (hno L1 b1) hpc
    (noPre hP h hnoE T hsp h28 hm h0 (by rw [e30]; exact hra4) (by rw [e30]; exact hra) hcost) ?_
  intro S1 _ hpost hrg1
  obtain ⟨ptr, junk, f, v, m, ex, ep, rfl, hA⟩ := noPost hP h T hsp h28 hm h0 S1 hrg1 hpost
  exact KC T ptr junk f v m ex ep hA

end

end FvModexp.Arm64.P2W2
