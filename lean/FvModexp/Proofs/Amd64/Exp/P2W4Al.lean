import FvModexp.Proofs.Amd64.Exp.P2W4WC
import FvModexp.Proofs.Amd64.Nat.StackNatCall
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `runtime.makeslice` / `runtime.newobject` called at `RSP = sp - 0x8` under `WC`
(agent divmc s76, port of divmc s69; amd64 twin of agent infra's `Arm64.P2W4Al`, adapted from agent asm's amd64 `EvMv`)

* `WC.alloc`, `AllocR`, `mkCall`: `makeslice(Word, n, c)` (`RAX = type:big.Word`, `RBX = n`, `RCX = c`);
* `noCall`: `newobject(type:[1]big.Word)` (`RAX = 0x6ed740`, 8 bytes, no pointers) — the `nat{1}` of `return 1`.
The callee's window `calleeStack64 = [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)]` lies in `WN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

abbrev mkE : Nat := 4739904
abbrev noE : Nat := 4331392
theorem mkE_eq : cA "runtime.makeslice" = mkE := by decide
theorem noE_eq : cA "runtime.newobject" = noE := by decide
theorem wT_eq' : StackNat.wT = 7233184 := by decide
/-- `type:[1]big.Word` (the `nat{1}` literal) -/
abbrev oT : Nat := 7264064

theorem oT_facts {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE oT 8 = 8 ∧ m.readLE (oT + 8) 8 = 0 ∧ m.accessible oT 16 false = true :=
  ⟨Janus.Amd64.Tactic.readLE_of_dataRead hd (by decide +kernel),
    Janus.Amd64.Tactic.readLE_of_dataRead hd (by decide +kernel), StackNat.accessible_of_dataRead' hd (by decide +kernel)⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

theorem cs_out {a k : Nat} {cs : List (Nat × Nat)} (hcs : ∀ q ∈ cs, sp - 0x8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x2f8)
    (ho : Outside a k (WN sp K)) : Outside a k cs := by
  simp only [WN, outside_cons, outside_nil, and_true] at ho
  refine outside_of_forall fun q hq => ?_
  have := hcs q hq; omega

theorem hdr_keep (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - 0x8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x2f8) (hLF : LiveFrame M m L1 []) {a k : Nat} (h1 : st ≤ a)
    (h2 : a + k ≤ st + 24) : m.readLE a k = M.readLE a k := by
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  unfold Apart at hstw
  rcases h.sok.2.1 with hL | hO
  · exact hLF.readLE a k (hL.sub h1 h2) trivial
  · refine hMF.readLE a k ?_
    rw [outside_append]
    refine ⟨hO.of_sub h1 h2, outside_of_forall fun q hq => ?_⟩
    have := hcs q hq; omega

/-- **`WC` through a live allocation** of `[p, p + n)` -/
theorem WC.alloc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - 0x8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x2f8) (hLF : LiveFrame M m L1 []) (hrg : m.regions = M.regions)
    {p n : Nat} (hin : InRanges p n R.rt) (hap : ApartAll p n L1) (hn : n ≤ b1)
    (hinv : R.inv (b1 + stkR H M st - n) (L1 ++ [(p, p + n)]) g (view R.rt (L1 ++ [(p, p + n)]) m)) :
    WC R H L K g sp st zp zc s.mem m (L1 ++ [(p, p + n)]) (b1 - n) ℓ := by
  have e0 : stW m st = stW M st := hdr_keep hP h hMF hcs hLF (Nat.le_refl _) (by omega)
  have e1 : stLen m st = stLen M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have e2 : stCap m st = stCap M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + n)]) :=
    LiveExt.single (by rw [show p + n - p = n by omega]; exact hin) (by rw [show p + n - p = n by omega]; exact hap)
  have hinv' : R.inv (b1 - n + stkR H m st) (L1 ++ [(p, p + n)]) g (view R.rt (L1 ++ [(p, p + n)]) m) := by
    rw [stkR_congr e2, show b1 - n + stkR H M st = b1 + stkR H M st - n by omega]; exact hinv
  refine h.call hMF hLF hrg (fun a k _ o2 _ _ => cs_out hcs o2) (fun _ _ _ _ => trivial) hx hinv'
    (stkOK_hdr h.sok hMF e0 e1 e2 hx) (e1.trans h.len) (Nat.le_refl _) (Or.inl ⟨e0, e2⟩)
    (fun hn => absurd ⟨e0, e2⟩ hn)

theorem alloc_rd {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - 0x8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x2f8) (hLF : LiveFrame M m L1 []) {a k : Nat}
    (hh : Held R L1 a k) (hap : Apart a k (sp - 0x8 - K) (K + 0x360)) : m.readLE a k = M.readLE a k := by
  rcases hh with hL | hO
  · exact hLF.readLE a k hL trivial
  · refine hMF.readLE a k ?_
    rw [outside_append]
    unfold Apart at hap
    refine ⟨hO, outside_of_forall fun q hq => ?_⟩
    have := hcs q hq; omega

end

/-- the facts after a live allocation of `[p, p + rr)` (`n` bytes asked) at a call from `RSP = sp - 0x8`, memory `M → m` -/
structure AllocR (R : RtInv) (H : Nat) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory)
    (L1 : List (Nat × Nat)) (b1 ℓ : Nat) (m : Memory) (p rr n : Nat) : Prop where
  wc : WC R H L K g sp st zp zc m0 m (L1 ++ [(p, p + rr)]) (b1 - rr) ℓ
  rin : InRanges p rr R.rt
  rap : ApartAll p rr L1
  b48 : p + rr ≤ 2 ^ 48
  acc : m.accessible p rr true = true
  al : p % 8 = 0
  sz : n ≤ rr
  rc : rr ≤ allocCost n
  keep : ∀ a k, (sp - 0x8 ≤ a ∧ a + k ≤ sp ∨ sp + 0x18 ≤ a ∧ a + k ≤ sp + 0x358) → m.readLE a k = M.readLE a k
  rdH : ∀ a k, Held R L1 a k → Apart a k (sp - 0x8 - K) (K + 0x360) → m.readLE a k = M.readLE a k
  macc : ∀ a k w, m.accessible a k w = M.accessible a k w

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`makeslice(Word, n, c)` from `RSP = sp - 0x8`** (continuation form) -/
theorem mkCall {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    {n c : Nat} (hnc : n ≤ c) (hc0 : 0 < c) (hc : c ≤ 2 ^ 17) (hcost : blockSize (8 * c) true ≤ b1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mkE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hm : T.mem = M) (hra : M.readLE (sp - 0x8) 8 < 2 ^ 47)
    (h0 : T.regs 0 = BitVec.ofNat 64 7233184) (h3 : T.regs 3 = BitVec.ofNat 64 n) (h1 : T.regs 1 = BitVec.ofNat 64 c)
    (KC : ∀ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64),
      AllocR R H L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize (8 * c) true) (8 * c) →
      ReachesRet (LibW.program.link impl) ret0 (retState64 T junk [ptr] f x yh m zh kr) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hce := h.cenv hP
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -, -, -, -, -, -, -⟩ := hce
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts c12
  rw [wT_eq'] at ht1 ht2 ht3
  have t4 : (T.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t14 : (T.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have t0 : (T.regs 0).toNat = 7233184 := by rw [h0]; rfl
  have t3 : (T.regs 3).toNat = n := by rw [h3, BitVec.toNat_ofNat]; omega
  have t1 : (T.regs 1).toNat = c := by rw [h1, BitVec.toNat_ofNat]; omega
  have hsz : typSize T.mem (T.regs 0).toNat * (T.regs 1).toNat = 8 * c := by
    simp only [typSize, t0, t1, hm, ht1]
  have hround : makesliceRound64 T = blockSize (8 * c) true := by
    simp only [makesliceRound64, typSize, typNoscan, typPtrBytes, t0, t1, hm, ht1, ht2]; rfl
  have hacc : M.accessible (sp - 0x8 - 4096) (4096 + 8 + 8 * 3) true = true :=
    Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)
  have hwT : Apart 7233184 16 (sp - 0x8 - 4096) (4096 + 8 + 8 * 3) :=
    apart_of_data c12 1 (by decide) (by decide) hacc
  have hok : R.ok mkE [7233184, n, c] := by rw [← mkE_eq]; exact hsv.1 _ _ _ hc
  unfold Apart at hwT c9
  have hinv := h.inv
  refine ReachesRet.call_regions (hmk.pos L1 (b1 + stkR H M st)) hpc ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
  · rw [t4, hm]; exact hra
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4, hm]; exact hacc
  · rw [t0, hm]; exact ⟨by decide, ht3⟩
  · rw [t3, t1]; exact hnc
  · rw [t1]; omega
  · rw [hsz]; simp only [maxAlloc]; omega
  · simp only [calleeStack64, t0, t4, outside_cons, outside_nil, and_true]; omega
  · simp only [GuardOK64, t14, t4, hm]; exact ⟨c5, c6, by omega⟩
  · simp only [calleeStack64, t14, t4, outside_cons, outside_nil, and_true]; omega
  · rw [t0, t3, t1]; exact hok
  · rw [t14, hm]; exact hinv
  · rw [hround]; omega
  · intro q hq
    have := c11 q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
  · rw [hsz]; omega
  intro S1 _ hpost hrg1
  obtain ⟨ptr, junk, f, x, yh, m, zh, kr, rfl, hMF, hLF, ⟨hobj, hap⟩, -, hinv⟩ := hpost
  simp only [makesliceObj64, Fresh, hsz] at hobj
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, hm, ht2]; rfl
  rw [hround] at hap hinv
  rw [hns] at hobj
  obtain ⟨hin, h48, hacc', hal, -, -, hle⟩ := hobj
  have hcs : ∀ q ∈ calleeStack64 T 4096 3, sp - 0x8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x2f8 := by
    intro q hq; simp only [calleeStack64, t4, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  rw [hm] at hMF hLF
  rw [t14] at hinv
  have hrg : m.regions = M.regions := by rw [← hm]; exact hrg1
  have hout := hP.win_rt
  have hbs : blockSize (8 * c) true ≤ b1 := hcost
  refine KC ptr junk f x yh m zh kr ⟨h.alloc hP hMF hcs hLF hrg hin hap hbs hinv, hin, hap, h48, hacc',
    hal (Or.inr (by omega)), hle, blockSize_le_allocCost _ _, fun a k ha => hMF.readLE a k ?_,
    fun a k hh hap => alloc_rd hMF hcs hLF hh hap, hMF.accessible⟩
  rw [outside_append]
  refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
  simp only [calleeStack64, t4, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`newobject(type:[1]big.Word)` from `RSP = sp - 0x8`** (continuation form) -/
theorem noCall {impl : List Amd64.Segment} (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hcost : blockSize 8 true ≤ b1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 noE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hm : T.mem = M) (hra : M.readLE (sp - 0x8) 8 < 2 ^ 47)
    (h0 : T.regs 0 = BitVec.ofNat 64 oT)
    (KC : ∀ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64),
      AllocR R H L K g sp st zp zc s.mem M L1 b1 ℓ m ptr.toNat (blockSize 8 true) 8 → ZeroBytes m ptr.toNat 8 →
      ReachesRet (LibW.program.link impl) ret0 (retState64 T junk [ptr] f x yh m zh kr) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hce := h.cenv hP
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -, -, -, -, -, -, -⟩ := hce
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  obtain ⟨ht1, ht2, ht3⟩ := oT_facts c12
  have t4 : (T.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have t14 : (T.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have t0 : (T.regs 0).toNat = oT := by rw [h0]; rfl
  have hsz : typSize T.mem (T.regs 0).toNat = 8 := by simp only [typSize, t0, hm, ht1]
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, hm, ht2]; rfl
  have hround : newobjectRound64 T = blockSize 8 true := by simp only [newobjectRound64, hsz, hns]
  have hacc : M.accessible (sp - 0x8 - 4096) (4096 + 8 + 8 * 1) true = true :=
    Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)
  have hwT : Apart oT 16 (sp - 0x8 - 4096) (4096 + 8 + 8 * 1) :=
    apart_of_data c12 2 (by decide) (by decide) hacc
  have hinv := h.inv
  unfold Apart at hwT c9
  refine ReachesRet.call_regions (hno L1 (b1 + stkR H M st)) hpc ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_⟩, hsv.2.2.2.2.1 _, ?_, ?_, ?_, ?_⟩ ?_
  · rw [t4, hm]; exact hra
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4, hm]; exact hacc
  · rw [t0]; decide
  · rw [t0, hm]; exact ht3
  · rw [hsz]; simp only [maxAlloc]; omega
  · simp only [calleeStack64, t0, t4, outside_cons, outside_nil, and_true]; omega
  · rw [t14]; omega
  · rw [t14, hm]; exact c6
  · rw [t14, t4, hm]; omega
  · simp only [calleeStack64, t14, t4, outside_cons, outside_nil, and_true]; omega
  · rw [t14, hm]; exact hinv
  · rw [hround]; omega
  · intro q hq
    have := c11 q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
  intro S1 _ hpost hrg1
  obtain ⟨ptr, junk, f, x, yh, m, zh, kr, rfl, hMF, hLF, hQ, -, hinv⟩ := hpost
  rw [hsz] at hQ
  obtain ⟨hobj, hap⟩ := hQ (by omega)
  simp only [newobjectObj64, Fresh, hsz, hns] at hobj
  rw [hround] at hap hinv
  obtain ⟨hin, h48, hacc', hal, -, hz, hle⟩ := hobj
  have hcs : ∀ q ∈ calleeStack64 T 4096 1, sp - 0x8 - K ≤ q.1 ∧ q.2 ≤ sp + 0x2f8 := by
    intro q hq; simp only [calleeStack64, t4, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  rw [hm] at hMF hLF
  rw [t14] at hinv
  have hrg : m.regions = M.regions := by rw [← hm]; exact hrg1
  have hout := hP.win_rt
  refine KC ptr junk f x yh m zh kr ⟨h.alloc hP hMF hcs hLF hrg hin hap hcost hinv, hin, hap, h48, hacc',
    hal (by simp), hle, blockSize_le_allocCost _ _,
    fun a k ha => hMF.readLE a k ?_, fun a k hh hap => alloc_rd hMF hcs hLF hh hap, hMF.accessible⟩
    (hz trivial)
  rw [outside_append]
  refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
  simp only [calleeStack64, t4, outside_cons, outside_nil, and_true]; omega

end

end FvModexp.Amd64.P2W4
