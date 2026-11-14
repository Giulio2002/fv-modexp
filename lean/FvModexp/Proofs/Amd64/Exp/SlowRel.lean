import FvModexp.Proofs.Amd64.Exp.SlowDefs
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the shared context `WC` and the callee-step lemmas (agent expmc s78: asm's amd64 `ExpEven` EvRel
(s57) ported to the slow frame: constants `0x140 … 0x1c0` + `0x68`, callee `above ≤ 0x70`, no `natOne`)

`WC R L K g sp st zp zc m0 M L1 b1 ℓ`: the memory `M` at a point of the function (entry memory `m0`, entry live set
`L`) differs from `m0` only in the runtime ranges, the function's window `WN` (`[sp - 8 - K, sp + 0x1b0)` = callee
stacks, frame, saved `BP`; and the register spill area `[sp + 0x1e8, sp + 0x220)`; NOT the return address and the
stack arguments `[sp + 0x1b0, sp + 0x1e8)`) and `ZS` (`z`'s array, the stack header, the entry free part of the
stack's array). Callees run at `RSP = sp - 8` with window `win = [sp - 8 - stk, sp - 8 + above)`, `stk ≤ K`,
`above ≤ 0x70` (so the slots `[sp + 0x68, sp + 0x220)` survive every call).

Every segment module imports this module directly (ROW-TIME rule). Contents: `ra_slow`; `WC` and its transport
(`WC.frame`, `WC.call`, `WC.stkNat`, `stepC`, `nonStk`); reads (`WC.read`, `WC.readB`, `oe_bytes`, `obj_at`,
`WC.globals`); callee preconditions (`WC.cenv`, `snPre`); the local-nat layer `Loc`/`Ob`/`DL`/`LN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

set_option maxRecDepth 20000 in
/-- a return address inside the function's segment (`seg20`, base `0x5e7a20`) is a return address of every callee
program without the function -/
theorem ra_slow {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x84d) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (6191648 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg20) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg20.name = fn by decide]; exact hn) i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5e7a20 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg20] using this

/-- the window ranges the function (and its callees) write -/
@[reducible] def WN (sp K : Nat) : List (Nat × Nat) := [(sp - 8 - K, sp + 0x1b0), (sp + 0x1e8, sp + 0x220)]

/-- the caller-visible ranges the function writes: `z`'s array, the stack header and the entry free part -/
@[reducible] def ZS (zp zc st : Nat) (m0 : Memory) : List (Nat × Nat) := [(zp, zp + 8 * zc)] ++ stkWs m0 st

/-- the context at every point after the entry (see the module doc) -/
structure WC (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory) (L1 : List (Nat × Nat))
    (b1 ℓ : Nat) : Prop where
  fr : MemFrame m0 M (R.rt ++ WN sp K ++ ZS zp zc st m0)
  lf : LiveFrame m0 M L (ZS zp zc st m0)
  rg : M.regions = m0.regions
  le : LiveExt R L L1
  inv : R.inv b1 L1 g (view R.rt L1 M)
  sok : StkOK M R L1 st
  len : stLen M st = ℓ
  lo : stLen m0 st ≤ ℓ
  lc0 : stLen m0 st ≤ stCap m0 st
  kf : ArrKF R L st m0 M
  ain : ArrIn L1 st m0 M

/-- a read whose every byte is outside the frame's ranges -/
theorem MemFrame.bytewise {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a n : Nat}
    (hb : ∀ i, i < n → Outside (a + i) 1 rs) : m'.readLE a n = m.readLE a n := by
  apply Janus.Arm64.Memory.readLE_congr
  intro i hi
  have := h.readLE (a + i) 1 (hb i hi)
  simp only [Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

/-- a held range: every byte outside the extra ranges keeps its value -/
theorem held_bytesW {rt L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (hh : InRanges a n L ∨ Outside a n rt) (hf : MemFrame m m' (rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (h : ∀ i, i < n → Outside (a + i) 1 ws1 ∧ Outside (a + i) 1 ws2) : m'.readLE a n = m.readLE a n := by
  apply Janus.Arm64.Memory.readLE_congr
  intro i hi
  have hh1 : InRanges (a + i) 1 L ∨ Outside (a + i) 1 rt :=
    hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have := Expmc.held_readLE hh1 hf hl (h i hi).1 (h i hi).2
  simp only [Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

/-- a fresh range is apart from every held range -/
theorem hfresh {R : RtInv} {L : List (Nat × Nat)} {a n ptr k : Nat} (h : Held R L a n)
    (hAp : ApartAll ptr k L) (hIn : InRanges ptr k R.rt) : Apart ptr k a n := by
  rcases h with hL | ho
  · exact hAp.apart_of_inRanges hL
  · exact (hIn.apart ho).symm

/-! ## `WC`: generic transport -/

section
variable {R : RtInv} {L : List (Nat × Nat)} {K g sp st zp zc : Nat} {m0 M : Memory} {L1 : List (Nat × Nat)}
    {b1 ℓ : Nat}

/-- a held range (live in `L` or outside the runtime) outside the entry free part is apart from the free part now -/
theorem free_apart (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hf : Apart a k (free m0 st).1 (free m0 st).2) : Apart a k (free M st).1 (free M st).2 := by
  have hc := h.sok.2.2.2.2.2.1
  have hl := h.len
  have hlo := h.lo
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    simp only [Apart] at hf ⊢; rw [e1, e2]; omega
  · have : a + k ≤ stW M st ∨ stW M st + 8 * stCap M st ≤ a := by
      rcases hh with hL | hO
      · have := hap.apart_of_inRanges hL; omega
      · have := hin.apart hO; unfold Apart at this; omega
    show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    unfold Apart; omega

/-- a held range outside `ZS` is outside the stack's writable ranges now -/
theorem stk_out (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (ho : Outside a k (ZS zp zc st m0)) : Outside a k (stkWs M st) := by
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
  refine ⟨ho.2.1, ?_⟩
  have := h.lc0
  have := free_apart h hh (by simp only [Apart]; omega)
  simp only [Apart] at this
  have hc := h.sok.2.2.2.2.2.1
  omega

/-- the read form: a held range outside the window and `ZS` keeps its bytes -/
theorem WC.read (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hw : Outside a k (WN sp K)) (ho : Outside a k (ZS zp zc st m0)) : M.readLE a k = m0.readLE a k :=
  Expmc.held_readLE hh h.fr h.lf hw ho

/-- byte-wise read through `WC` -/
theorem WC.readB (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat} (hh : InRanges a k L ∨ Outside a k R.rt)
    (hb : ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st m0)) :
    M.readLE a k = m0.readLE a k :=
  held_bytesW hh h.fr h.lf hb

/-- a range outside everything the function may write is outside the runtime and the stack's writable ranges now -/
theorem out_all (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {a k : Nat}
    (ho : Outside a k (R.rt ++ WN sp K ++ ZS zp zc st m0)) :
    Outside a k R.rt ∧ Outside a k (WN sp K) ∧ Outside a k (stkWs M st) := by
  rw [outside_append, outside_append] at ho
  exact ⟨ho.1.1, ho.1.2, stk_out h (Or.inr ho.1.1) ho.2⟩

/-- `WC` through a step that writes `ws` and keeps the stack header (the function's own stores, a callee that
does not change the stack object) -/
theorem WC.frame (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {M' : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hsub : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st m0) → Outside a k ws)
    (hL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st m0) → Outside a k ws)
    (hhd : Outside st 24 ws) (hws : ∀ r ∈ ws, InRanges r.1 (r.2 - r.1) L1 ∨ Outside r.1 (r.2 - r.1) R.rt) :
    WC R L K g sp st zp zc m0 M' L1 b1 ℓ := by
  have e0 : stW M' st = stW M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M' st = stLen M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M' st = stCap M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  refine ⟨h.fr.trans hF fun a k ho => ⟨ho, hsub a k ho⟩,
    ⟨fun a k hin ho => by rw [hF.readLE a k (hL a k hin ho), h.lf.readLE a k hin ho]⟩, hrg.trans h.rg, h.le,
    Expmc.inv_frame hF hws h.inv, stkOK_hdr h.sok hF e0 e1 e2 (LiveExt.refl R L1), by rw [e1]; exact h.len, h.lo, h.lc0,
    ?_, ?_⟩
  · rcases h.kf with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨e0.trans a1, e2.trans a2⟩
    · exact Or.inr (by rw [e0, e2]; exact ⟨a1, a2⟩)
  · exact h.ain.congr e0 e2 fun _ hr => hr

/-- `WC` through a callee whose post has a new live set `L2`, budget `b2` and stack level `ℓ'` -/
theorem WC.call (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {M' : Memory} {ws ws' : List (Nat × Nat)}
    {L2 : List (Nat × Nat)} {b2 ℓ' : Nat}
    (hF : MemFrame M M' (R.rt ++ ws)) (hLF : LiveFrame M M' L1 ws') (hrg : M'.regions = M.regions)
    (hsub : ∀ a k, Outside a k R.rt → Outside a k (WN sp K) → Outside a k (stkWs M st) →
      Outside a k (ZS zp zc st m0) → Outside a k ws)
    (hL : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st m0) → Outside a k ws')
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hok : StkOK M' R L2 st)
    (hlen : stLen M' st = ℓ') (hle : ℓ ≤ ℓ')
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1))
    (hmem : ArrIn L2 st M M') :
    WC R L K g sp st zp zc m0 M' L2 b2 ℓ' := by
  have hLL : ∀ r ∈ L, r ∈ L1 := fun r hr => h.le.mem_old hr
  refine ⟨h.fr.trans hF fun a k ho => ⟨ho, ?_⟩, ⟨fun a k hin ho => ?_⟩, hrg.trans h.rg, h.le.trans hx, hinv, hok,
    hlen, by have := h.lo; omega, h.lc0, ?_, h.ain.trans hmem hx⟩
  · obtain ⟨o1, o2, o3⟩ := out_all h ho
    rw [outside_append, outside_append] at ho
    rw [outside_append]
    exact ⟨o1, hsub a k o1 o2 o3 ho.2⟩
  · rw [hLF.readLE a k (h.le.inRanges_old hin) (hL a k hin ho), h.lf.readLE a k hin ho]
  · rcases harr with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rcases h.kf with ⟨b1', b2'⟩ | ⟨b1', b2'⟩
      · exact Or.inl ⟨a1.trans b1', a2.trans b2'⟩
      · exact Or.inr (by rw [a1, a2]; exact ⟨b1', b2'⟩)
    · exact Or.inr ⟨a1, fun r hr => a2 r (hLL r hr)⟩

/-- a scratch nat of a callee (relative to the call memory `M`) is one relative to the entry -/
theorem Scr.rebase (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ) {L2 : List (Nat × Nat)} {M' : Memory} {t k : Nat}
    (hs : Scr R L1 L2 M M' st t k) : Scr R L L2 m0 M' st t k := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  refine ⟨s1, s2, s3, s4, ?_⟩
  have hl := h.len
  have hlo := h.lo
  rcases s5 with ⟨c0, c1, c2⟩ | ⟨c1, c2⟩
  · rcases h.kf with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · left; rw [← e1, ← e2]; exact ⟨c0, by omega, c2⟩
    · right; exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
  · right; exact ⟨c1, fun r hr => c2 r (h.le.mem_old hr)⟩

end

/-! ## Entry facts used by the transport lemmas -/

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

theorem EPre.cenv0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    CallW.CEnv R L g fs (sp - 8) K 0x228 s.mem :=
  hP.1.2.2.2.2.2.2.2.2.1

theorem EPre.kf (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    41512 ≤ K ∧ K ≤ 2 ^ 20 ∧ K + 8 ≤ sp ∧ sp % 8 = 0 ∧ sp + 0x220 ≤ 2 ^ 48 := by
  obtain ⟨⟨-, -, -, -, -, h6, h7, h8, ⟨-, c2, c3, -⟩, -⟩, -⟩ := hP
  omega

theorem EPre.win_rt (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    Outside (sp - 8 - K) (K + 0x228) R.rt :=
  hP.cenv0.2.2.2.2.2.2.2.1

theorem EPre.stk0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) : StkOK s.mem R L st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP
  exact h

theorem EPre.cap0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    stCap s.mem st = 0 → stW s.mem st = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, -, -, -, -, -, -, -, h⟩, -⟩ := hP
  exact h

/-- the stack header / array facts of the entry -/
theorem EPre.stkF (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    Apart st 24 (sp - 8 - K) (K + 0x228) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
    (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x228) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
    s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
    Apart st 24 (free s.mem st).1 (free s.mem st).2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3, h4, h5, h6, h7, -⟩ := hP
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `z`'s facts (non-empty `z`) -/
theorem EPre.zF (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    0 < zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart (fs - 8) 8 zp (8 * zc) ∧ Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧
    Apart zp (8 * zc) RunIface.gA 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP
  exact h

/-- every range the function writes (besides the runtime's) is writable at the entry -/
theorem EPre.ws_acc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    ∀ r ∈ WN sp K ++ ZS zp zc st s.mem, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
  have hk := hP.kf
  have hacc := hP.cenv0.2.2.2.1
  have hz := hP.zF
  have k3 := hP.stk0.2.2.1
  have k5 := hP.stk0.2.2.2.2.1
  intro r hr hlt
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only at hlt ⊢
  · exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact (hz (by omega)).2.1
  · rw [show st + 24 - st = 24 by omega]; exact k3
  · exact Janus.Arm64.Memory.accessible_mono _ (k5 (by omega)).2.2.1 (by omega) (by omega)

/-- an 8-byte word outside the runtime, the window, `z`, the stack header and array has every byte outside the
function's writes -/
theorem EPre.w_out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {a : Nat}
    (hrt : Outside a 8 R.rt) (hw : Apart a 8 (sp - 8 - K) (K + 0x228)) (hz : 0 < zc → Apart a 8 zp (8 * zc))
    (hst : Apart st 24 a 8) (har : 0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) a 8) :
    ∀ i, i < 8 → Outside (a + i) 1 (R.rt ++ WN sp K ++ ZS zp zc st s.mem) := by
  have hk := hP.kf
  have hlc := hP.stk0.2.2.2.2.2.1
  intro i hi
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
    and_true]
  unfold Apart at hw hst
  refine ⟨⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩, ?_, by omega, ?_⟩
  · rcases Nat.eq_zero_or_pos zc with h0 | h0
    · subst h0; omega
    · have := hz h0; unfold Apart at this; omega
  · rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · omega
    · have := har h0; unfold Apart at this; omega

theorem EPre.g_out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    ∀ i, i < 8 → Outside (g + 16 + i) 1 (R.rt ++ WN sp K ++ ZS zp zc st s.mem) := by
  have hc := hP.cenv0
  have hs := hP.stkF
  exact hP.w_out hc.2.2.2.2.2.2.2.2.2.1 (by have := hc.2.2.2.2.2.2.2.2.1; unfold Apart at this ⊢; omega)
    (fun h0 => (hP.zF h0).2.2.2.2.1) (by have := hs.2.1; unfold Apart at this ⊢; omega)
    (fun h0 => (hs.2.2.2.1 h0).2.1)

theorem EPre.fs_out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) :
    ∀ i, i < 8 → Outside (fs - 8 + i) 1 (R.rt ++ WN sp K ++ ZS zp zc st s.mem) := by
  have hc := hP.cenv0
  have hs := hP.stkF
  exact hP.w_out hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (fun h0 => (hP.zF h0).2.2.2.2.2.1) hs.2.2.1 (fun h0 => (hs.2.2.2.1 h0).2.2)

/-- the bytes of an entry object (`OE`, apart from `z` when `z` is not empty) are outside the function's writes -/
theorem oe_bytes (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {a k : Nat}
    (hoe : OE R L sp K st s.mem a k) (hza : 0 < zc → Apart zp (8 * zc) a k) :
    ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st s.mem) := by
  have hk := hP.kf
  obtain ⟨-, h2, h3, h4⟩ := hoe
  intro i hi
  simp only [Apart] at h2 h3 h4
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨by omega, by omega⟩, ?_, by omega, by omega⟩
  rcases Nat.eq_zero_or_pos zc with h0 | h0
  · subst h0; omega
  · have := hza h0; unfold Apart at this; omega

end

/-! ## Callee environment, stack object, inputs, globals -/

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the callee environment at `RSP = sp - 8` (window `[sp - 8 - K, sp + 0x68)`) -/
theorem WC.cenv (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) : CallW.CEnv R L1 g fs (sp - 8) K 0x70 M := by
  have hgM : M.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := MemFrame.bytewise h.fr hP.g_out
  have hfM : M.readLE (fs - 8) 8 = s.mem.readLE (fs - 8) 8 := MemFrame.bytewise h.fr hP.fs_out
  have hws := hP.ws_acc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19⟩ := hP.cenv0
  refine ⟨c1, c2, by omega, by rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega),
    c5, by rw [h.fr.accessible]; exact c6, by rw [hgM]; exact c7, c8.of_sub (by omega) (by omega),
    by unfold Apart at c9 ⊢; omega, c10, ?_,
    dataLoaded_frame64 c12 h.rg c13 (by rw [← List.append_assoc]; exact h.fr) hws, c13, c14, c15,
    by rw [h.fr.accessible]; exact c16, by rw [hfM]; exact c17, c18, by unfold Apart at c19 ⊢; omega⟩
  refine h.le.liveSep (LiveSep.sub_win c11 (by omega) (by omega)) fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr; simp only
  exact c8.of_sub (by omega) (by omega)

/-- `(*stack).nat(n)`'s precondition at `RSP = sp - 8` -/
theorem snPre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above n : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x70)
    {S1 : State} (hsp : (S1.regs 4).toNat = sp - 8) (h14 : (S1.regs 14).toNat = g) (hfs : S1.fsBase.toNat = fs)
    (hm : S1.mem = M) (hn : n ≤ 2 ^ 16) (hl : ℓ + n + 3 ≤ 2 ^ 16) (hb : stackNatCost ℓ n ≤ b1) :
    StackNat.Pre R b1 L1 stk above st n S1 := by
  have hce := h.cenv hP
  have hk := hP.kf
  have hout := hP.win_rt
  obtain ⟨hstw, hstg, -, harr, hwbf, hwbA, hsf⟩ := hP.stkF
  have hsv := hP.1.2.2.2.2.2.2.2.2.2
  have hheld := hP.stk0.2.1
  subst hm
  unfold Apart at hstw
  refine ⟨CallW.callEnv_of hce hsp h14 hfs rfl hstk habove (by omega), hsv, h.sok, ?_, fun hc0 => ?_, hn,
    by rw [h.len]; omega, by rw [h.len]; exact hb, by rw [h14]; exact h.inv, by rw [h.fr.accessible]; exact hwbf,
    hwbA, free_apart h hheld hsf⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rw [h14]
    rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc0; rw [e1, e2]
      obtain ⟨o1, o2, -⟩ := harr hc0
      unfold Apart at o1
      refine ⟨?_, o2⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
    · have a1 := hin.apart hout
      have a2 := hin.apart hce.2.2.2.2.2.2.2.2.2.1
      unfold Apart at a1 a2 ⊢
      refine ⟨?_, by omega⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

set_option maxRecDepth 20000 in
/-- `WC` through `(*stack).nat(n)` called at `RSP = sp - 8` (`PostL`) -/
theorem WC.stkNat (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above n : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x70)
    {S1 s' : State} (hsp : (S1.regs 4).toNat = sp - 8) (h14 : (S1.regs 14).toNat = g) (hm : S1.mem = M)
    (hrg : s'.mem.regions = M.regions) (hn : 0 < n)
    (hpost : StackNat.PostL R b1 L1 stk above st n S1 s') :
    ∃ (L2 : List (Nat × Nat)) (b2 : Nat), b1 - stackNatCost ℓ n ≤ b2 ∧
      WC R L K g sp st zp zc s.mem s'.mem L2 b2 (ℓ + StackNat.rnd n) ∧
      Scr R L L2 s.mem s'.mem st (stW s'.mem st + 8 * ℓ) n ∧
      s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * ℓ) ∧ s'.regs 3 = BitVec.ofNat 64 n ∧
      s'.regs 1 = BitVec.ofNat 64 n ∧ s'.fsBase = S1.fsBase ∧ s'.df = S1.df ∧
      MemFrame M s'.mem (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ stkWs M st) ∧
      Scr R L1 L2 M s'.mem st (stW s'.mem st + 8 * ℓ) n ∧ LiveFrame M s'.mem L1 (stkWs M st) ∧ LiveExt R L1 L2 ∧
      ((stW s'.mem st = stW M st ∧ stCap s'.mem st = stCap M st) ∨
        (InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧ ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L1)) := by
  have hk := hP.kf
  obtain ⟨hfs, hdf, h0, h1, h2, L2, b2, ⟨hx, hb, hinv⟩, hok, hlen, hsame, hgrow, hF, hLF, hmemb⟩ := hpost
  subst hm
  rw [h14] at hinv
  rw [h.len] at hlen hsame hgrow hb h0
  have hF' : MemFrame S1.mem s'.mem (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ stkWs S1.mem st) := by
    simpa only [win, hsp] using hF
  have hsc : Scr R L1 L2 S1.mem s'.mem st (stW s'.mem st + 8 * ℓ) n :=
    Scr.of_post hok hlen hn hsame hgrow h.len.symm
  have harr : (stW s'.mem st = stW S1.mem st ∧ stCap s'.mem st = stCap S1.mem st) ∨
      (InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧ ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L1) := by
    by_cases hc : ℓ + StackNat.rnd n ≤ stCap S1.mem st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  refine ⟨L2, b2, hb, ?_, Scr.rebase h hsc, h0 hn, h1, h2, hfs, hdf, hF', hsc, hLF, hx, harr⟩
  refine h.call (ws := [(sp - 8 - stk, sp - 8 + above)] ++ stkWs S1.mem st) (by rwa [List.append_assoc] at hF')
    hLF hrg ?_ (fun a k hin ho => stk_out h (Or.inl hin) ho) hx hinv hok hlen (by omega) harr ?_
  · intro a k o1 o2 o3 o4
    rw [outside_append]
    refine ⟨?_, o3⟩
    simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢
    omega
  · exact ArrIn.of_nat hok.2.2.2.2.2.1 hlen hsame (fun hc => hmemb (by rw [h.len]; omega))

set_option maxRecDepth 20000 in
/-- an entry input nat `(p, n)` (`OE`, readable, normalised, apart from `z`) as a callee at `RSP = sp - 8` reads it -/
theorem obj_at (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p n : Nat} (hoe : OE R L sp K st s.mem p (8 * n)) (hacc : s.mem.accessible p (8 * n) false = true)
    (h48 : p + 8 * n ≤ 2 ^ 48) (hN : NatNorm s.mem p n) (hn : n ≤ 2 ^ 12)
    (hza : 0 < zc → Apart zp (8 * zc) p (8 * n))
    {S' : State} (hsp : (S'.regs 4).toNat = sp - 8) (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 0x70) :
    EvenHyp.RdIn R L1 S' stk above p n ∧ NatNorm M p n ∧ NHyp.StkApart M st p (8 * n) ∧
      natVal M p n = natVal s.mem p n := by
  have hk := hP.kf
  have hb := oe_bytes hP hoe hza
  have hoe' := hoe
  obtain ⟨o1, o2, o3, o4⟩ := hoe'
  subst hm
  have hv : natVal S'.mem p n = natVal s.mem p n := h.readB o1 hb
  refine ⟨⟨by omega, by rw [h.fr.accessible]; exact hacc, h48, h.le.held o1, ?_⟩, ?_, fun hn0 => ⟨o3, ?_⟩, hv⟩
  · unfold Apart at o2
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rcases Nat.eq_zero_or_pos n with h0 | hn0
    · exact Or.inl h0
    · have hne := hN.resolve_left (by omega)
      right
      rw [h.readB (o1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
        fun i hi => by have := hb (8 * (n - 1) + i) (by omega); rwa [← Nat.add_assoc] at this]
      exact hne
  · exact fun _ => free_apart h o1 o4

set_option maxRecDepth 20000 in
/-- the globals at `M`, outside any window `w` inside `[sp - 8 - K, sp + 0x220)` and the header -/
theorem WC.globals (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {w : List (Nat × Nat)} (hw : ∀ a n, Outside a n [(sp - 8 - K, sp + 0x220), (st, st + 24)] → Outside a n w) :
    RunIface.Globals R M w := by
  have hk := hP.kf
  have hzA : 0 < zc → Apart zp (8 * zc) RunIface.gA 32 := fun h0 => (hP.zF h0).2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, hwbA, -⟩ := hP.stkF
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgA, -⟩ := hP'
  have hb := oe_bytes hP hgA hzA
  have hgst := hgA.2.2.1
  obtain ⟨-, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, -⟩ := hP
  have hrd : ∀ j, j + 8 ≤ 32 → M.readLE (RunIface.gA + j) 8 = s.mem.readLE (RunIface.gA + j) 8 := fun j hj =>
    h.readB (Or.inr (g9.of_sub (by omega) (by omega))) fun i hi => by
      have := hb (j + i) (by omega); rwa [← Nat.add_assoc] at this
  simp only [wTop, outside_cons, outside_nil, and_true] at g10 g13
  have ewb : StackNat.wbA = RunIface.wbA := rfl
  rw [ewb] at hwbA
  unfold Apart at hgst hwbA
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [h.fr.accessible]; exact g8, g9,
    hw _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
    by rw [h.fr.accessible]; exact g11, g12, hw _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
  · rw [g5, hrd 8 (by omega), ← g5]; exact g1
  · rw [g6, hrd 16 (by omega), ← g6]; exact g2
  · rw [g7, hrd 24 (by omega), ← g7]; exact g3
  · have e : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
        RunIface.gA + 0 := rfl
    rw [e, hrd 0 (by omega)]; rw [← e]; exact g4

set_option maxRecDepth 20000 in
/-- the window is outside the runtime ranges and the stack's writable ranges (any level) -/
theorem win_out0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ a k, sp - 8 - K ≤ a → a + k ≤ sp + 0x220 → Outside a k (R.rt ++ stkWs M st) := by
  have hout := hP.win_rt
  have hk := hP.kf
  have hc0 := hP.cap0
  obtain ⟨hstw, -, -, harr, -⟩ := hP.stkF
  have hlc := h.sok.2.2.2.2.2.1
  intro a k h1 h2
  rw [outside_append]
  refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
  simp only [stkWs, outside_cons, outside_nil, and_true]
  unfold Apart at hstw
  refine ⟨by omega, ?_⟩
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · rcases Nat.eq_zero_or_pos (stCap s.mem st) with c0 | c0
    · have := hc0 c0; rw [e1, e2, this, c0]; omega
    · have := (harr c0).1
      rw [← e1, ← e2] at this; unfold Apart at this; omega
  · have := hin.apart (hout.of_sub (a := a) (n := k) (by omega) (by omega)); unfold Apart at this; omega

/-- a callee frame (runtime, the callee window `[sp - 8 - stk, sp - 8 + above)`, extra ranges `zs` apart from the
window, the stack's writable ranges) keeps the window above `sp - 8 + above` -/
theorem keepC (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory} {stk above : Nat} {zs : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ zs ++ stkWs M st))
    (hstk : stk ≤ K) (habove : above ≤ 0x70)
    (hzs : ∀ a k, sp - 8 - K ≤ a → a + k ≤ sp + 0x220 → Outside a k zs) :
    ∀ a k, sp - 8 + above ≤ a → a + k ≤ sp + 0x220 → M'.readLE a k = M.readLE a k := by
  have hk := hP.kf
  intro a k ha1 ha2
  refine hF.readLE a k ?_
  have h1 := win_out0 hP h a k (by omega) ha2
  have h2 := hzs a k (by omega) ha2
  rw [outside_append] at h1
  rw [outside_append, outside_append, outside_append]
  refine ⟨⟨⟨h1.1, ?_⟩, h2⟩, h1.2⟩
  simp only [outside_cons, outside_nil, and_true]
  omega

end

/-! ## byte-wise outside facts -/

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

theorem out_bytes {a k : Nat} {m0 : Memory}
    (ho : Outside a k ([(sp - 8 - K, sp + wTop), (zp, zp + 8 * zc)] ++ stkWs m0 st)) :
    ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st m0) := by
  intro i hi
  simp only [wTop, WN, ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
  omega

end

/-! ## Local nats: `Ob`, `Loc`, `DL`, `LN` and the generic callee step -/

/-- a nat array the function keeps using: held, in the used part of the current stack array or apart from it -/
@[reducible] def Ob (R : RtInv) (L1 : List (Nat × Nat)) (st : Nat) (M : Memory) (t k : Nat) : Prop :=
  Held R L1 t (8 * k) ∧
    ((stW M st ≤ t ∧ t + 8 * k ≤ stW M st + 8 * stLen M st) ∨ Apart t (8 * k) (stW M st) (8 * stCap M st))

theorem Ob.mono {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : Ob R L1 st M t k) (hx : LiveExt R L1 L2) (hl : stLen M st ≤ stLen M' st)
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1)) :
    Ob R L2 st M' t k := by
  refine ⟨hx.held h.1, ?_⟩
  rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]
    rcases h.2 with ⟨a1, a2⟩ | a
    · exact Or.inl ⟨a1, by omega⟩
    · exact Or.inr a
  · exact Or.inr (hfresh h.1 hap hin).symm

theorem Ob.back {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {t k : Nat}
    (h : Ob R L1 st M t k) (hx : LiveExt R L1 L2) (hsb : StackBack R L1 L2 st M M') : Ob R L2 st M' t k :=
  h.mono hx (by rw [hsb.2.1]; exact Nat.le_refl _) hsb.2.2

theorem Ob.free {R : RtInv} {L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : Ob R L1 st M t k)
    (hlc : stLen M st ≤ stCap M st) : Apart t (8 * k) (free M st).1 (free M st).2 := by
  show Apart t (8 * k) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
  rcases h.2 with ⟨a1, a2⟩ | a
  · unfold Apart; omega
  · unfold Apart at a ⊢; omega

theorem Ob.out {R : RtInv} {L1 : List (Nat × Nat)} {st : Nat} {M : Memory} {t k : Nat} (h : Ob R L1 st M t k)
    (hlc : stLen M st ≤ stCap M st) (hst : Apart t (8 * k) st 24) : Outside t (8 * k) (stkWs M st) := by
  have := h.free hlc
  simp only [free, Apart] at this hst
  simp only [stkWs, outside_cons, outside_nil, and_true]
  omega

/-- a held range outside a callee's explicit writes keeps its bytes -/
theorem keepH {R : RtInv} {L1 : List (Nat × Nat)} {M M' : Memory} {cw zs ws : List (Nat × Nat)} {a k : Nat}
    (hF : MemFrame M M' (R.rt ++ cw ++ zs ++ ws)) (hLF : LiveFrame M M' L1 (zs ++ ws))
    (hh : Held R L1 a k) (h1 : Outside a k cw) (h2 : Outside a k zs) (h3 : Outside a k ws) :
    M'.readLE a k = M.readLE a k := by
  rcases hh with hin | hrt
  · exact hLF.readLE a k hin (by rw [outside_append]; exact ⟨h2, h3⟩)
  · exact hF.readLE a k (by rw [outside_append, outside_append, outside_append]; exact ⟨⟨⟨hrt, h1⟩, h2⟩, h3⟩)

/-- entry-relative location of a local array: in the entry free part of the stack, or fresh -/
@[reducible] def Loc (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st t k : Nat) : Prop :=
  (0 < stCap m0 st ∧ stW m0 st + 8 * stLen m0 st ≤ t ∧ t + 8 * k ≤ stW m0 st + 8 * stCap m0 st) ∨
    (InRanges t (8 * k) R.rt ∧ ApartAll t (8 * k) L)

/-- a destination array `p[0:c]` at memory `M` (live set `L1`) -/
@[reducible] def DL (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L1 p c ∧ (0 < c → Loc R L m0 st p c ∧ Ob R L1 st M p c)

/-- a live local nat `p[0:l]` (cap `c`) of value `v` -/
@[reducible] def LN (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p l c v : Nat) : Prop :=
  DL R L m0 st M L1 p c ∧ l ≤ c ∧ natVal M p l = v ∧ NatNorm M p l

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the apartness facts of a located array -/
theorem Loc.ap (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {t k : Nat}
    (h : Loc R L s.mem st t k) :
    Apart t (8 * k) (sp - 8 - K) (K + 0x228) ∧ Apart t (8 * k) st 24 ∧ Apart t (8 * k) (g + 16) 8 ∧
      Apart t (8 * k) (fs - 8) 8 ∧ (0 < zc → Apart t (8 * k) zp (8 * zc)) := by
  have hout := hP.win_rt
  have hc := hP.cenv0
  obtain ⟨-, -, -, harr, -, -, hsf⟩ := hP.stkF
  have hz := hP.zF
  have hsok := hP.stk0
  rcases h with ⟨c0, l1, l2⟩ | ⟨hin, hap⟩
  · obtain ⟨a1, a2, a3⟩ := harr c0
    simp only [Apart] at a1 a2 a3 hsf ⊢
    refine ⟨by omega, by omega, by omega, by omega, fun hz0 => ?_⟩
    have := (hz hz0).1.2.2.2
    simp only [Apart] at this; omega
  · exact ⟨(hin.apart hout).symm, hfresh hsok.2.1 hap hin, (hin.apart hc.2.2.2.2.2.2.2.2.2.1).symm,
      (hin.apart hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm, fun hz0 => hfresh (hz hz0).1.1 hap hin⟩

/-- the stack's array is `0` when empty (entry fact, kept or fresh with `0 < cap`) -/
theorem WC.cap0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    stCap M st = 0 → stW M st = 0 := by
  intro h0
  by_cases e : stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  · rw [e.1]; exact hP.cap0 (by rw [← e.2]; exact h0)
  · have := (h.ain e).2; omega

/-- `WC.call`'s obligations for a callee writing a located array -/
theorem Loc.sub {t k : Nat} (h : Loc R L s.mem st t k) :
    ∀ a n, Outside a n R.rt → Outside a n (ZS zp zc st s.mem) → Outside a n [(t, t + 8 * k)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨-, l1, l2⟩ | ⟨hin, -⟩
  · omega
  · have := hin.apart h1; unfold Apart at this; omega

theorem Loc.subL {t k : Nat} (h : Loc R L s.mem st t k) :
    ∀ a n, InRanges a n L → Outside a n (ZS zp zc st s.mem) → Outside a n [(t, t + 8 * k)] := by
  intro a n h1 h2
  simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at h2 ⊢
  rcases h with ⟨-, l1, l2⟩ | ⟨-, hap⟩
  · omega
  · have := hap.apart_of_inRanges h1; omega

end

/-- a fresh array (relative to `L1`, apart from the final stack array when that changed) is an `Ob` -/
theorem ob_fresh {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {p c : Nat}
    (hok : StkOK M R L1 st) (hc0 : stCap M st = 0 → stW M st = 0) (hin : InRanges p (8 * c) R.rt)
    (hap : ApartAll p (8 * c) L1) (hh : Held R L2 p (8 * c)) (hrs : ResSep M M' st p c) (hc : 0 < c) :
    Ob R L2 st M' p c := by
  refine ⟨hh, Or.inr ?_⟩
  by_cases e : stW M' st = stW M st ∧ stCap M' st = stCap M st
  · rw [e.1, e.2]
    rcases Nat.eq_zero_or_pos (stCap M st) with c0 | c0
    · rw [c0, hc0 c0]; unfold Apart; omega
    · exact hfresh (hok.2.2.2.2.1 c0).2.1 hap hin |>.symm |> fun h => h.symm
  · exact hrs hc e

/-- `LN` through a step keeping its bytes -/
theorem LN.keep {R : RtInv} {L : List (Nat × Nat)} {m0 : Memory} {st : Nat} {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {p l c v : Nat} (h : LN R L m0 st M L1 p l c v) (hx : LiveExt R L1 L2)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hb : 0 < c → ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k)
    (hob : 0 < c → Ob R L2 st M' p c) : LN R L m0 st M' L2 p l c v := by
  obtain ⟨⟨c40, hlv, hlo⟩, hlc, hv, hn⟩ := h
  refine ⟨⟨c40, fun hc => ?_, fun hc => ⟨(hlo hc).1, hob hc⟩⟩, hlc, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hlv hc
    exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩
  · rcases Nat.eq_zero_or_pos c with c0 | c0
    · have : l = 0 := by omega
      subst this
      rw [← hv]; exact Janus.Arm64.Memory.readLE_congr fun i hi => absurd hi (by omega)
    · rw [← hv]; exact hb c0 _ _ (Nat.le_refl _) (by omega)
  · rcases hn with h0 | hne
    · exact Or.inl h0
    · rcases Nat.eq_zero_or_pos c with c0 | c0
      · exact Or.inl (by omega)
      · right; rw [hb c0 _ _ (by omega) (by omega)]; exact hne

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- **the generic callee step**: the destination `(pd, cd)` is a located array or `z`'s, or an EMPTY range
(`cd = 0`); the callee runs at `RSP = sp - 8` with window `[sp - 8 - stk, sp - 8 + above)` -/
theorem stepC (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    (hds : ∀ a k, Outside a k R.rt → Outside a k (ZS zp zc st s.mem) → Outside a k [(pd, pd + 8 * cd)])
    (hdl : ∀ a k, InRanges a k L → Outside a k (ZS zp zc st s.mem) → Outside a k [(pd, pd + 8 * cd)])
    (hdw : Apart pd (8 * cd) (sp - 8 - K) (K + 0x228))
    {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x70)
    {M' : Memory} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st)) (hrg : M'.regions = M.regions)
    (hx : LiveExt R L1 L2) (hinv : R.inv b2 L2 g (view R.rt L2 M')) (hsb : StackBackL R L1 L2 st M M') :
    WC R L K g sp st zp zc s.mem M' L2 b2 ℓ ∧
    (∀ a k, sp - 8 + above ≤ a → a + k ≤ sp + 0x220 → M'.readLE a k = M.readLE a k) ∧
    (∀ q l c v, LN R L s.mem st M L1 q l c v → (0 < c → Apart q (8 * c) pd (8 * cd)) →
      LN R L s.mem st M' L2 q l c v) := by
  have hk := hP.kf
  have hzs : ∀ a k, sp - 8 - K ≤ a → a + k ≤ sp + 0x220 → Outside a k [(pd, pd + 8 * cd)] := by
    intro a k h1 h2
    simp only [outside_cons, outside_nil, and_true]
    have := hdw; unfold Apart at this; omega
  have hkc := keepC hP h hF hstk habove hzs
  have hw : WC R L K g sp st zp zc s.mem M' L2 b2 ℓ := by
    refine h.call (ws := [(sp - 8 - stk, sp - 8 + above)] ++ [(pd, pd + 8 * cd)] ++ stkWs M st)
      (by simpa only [List.append_assoc] using hF) hLF hrg ?_ ?_ hx hinv
      hsb.1.1 (hsb.1.2.1.trans h.len) (Nat.le_refl _) hsb.1.2.2 hsb.2
    · intro a k o1 o2 o3 o4
      rw [outside_append, outside_append]
      refine ⟨⟨?_, hds a k o1 o4⟩, o3⟩
      simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢; omega
    · intro a k hin ho
      rw [outside_append]
      exact ⟨hdl a k hin ho, stk_out h (Or.inl hin) ho⟩
  have hlc := h.sok.2.2.2.2.2.1
  refine ⟨hw, hkc, fun q l c v hq hqd => hq.keep hx hF.accessible (fun c0 a k h1 h2 => ?_)
    (fun c0 => ((hq.1.2.2 c0).2).back hx hsb.1)⟩
  obtain ⟨w1, w2, -, -, -⟩ := Loc.ap hP (hq.1.2.2 c0).1
  have hob := (hq.1.2.2 c0).2
  have hout := hob.out hlc w2
  unfold Apart at w1
  simp only [stkWs, outside_cons, outside_nil, and_true] at hout
  refine keepH (cw := [(sp - 8 - stk, sp - 8 + above)]) hF hLF (hob.1.sub h1 h2) ?_ ?_ ?_
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]
    have := hqd c0; unfold Apart at this; omega
  · simp only [stkWs, outside_cons, outside_nil, and_true]; omega

/-- the result of a callee (`NatRes`: the destination `(pd, cd)` reused, or fresh) is a live local nat -/
theorem LN.of_res (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {pd cd : Nat}
    (hd : DL R L s.mem st M L1 pd cd) {M' : Memory} {L2 : List (Nat × Nat)} {need p' l' c' v : Nat}
    (hr : EvenHyp.NatRes R L1 L2 M' pd cd need p' l' c' v) (hx : LiveExt R L1 L2)
    (hsb : StackBackL R L1 L2 st M M') (hrs : ResSep M M' st p' c') : LN R L s.mem st M' L2 p' l' c' v := by
  obtain ⟨hv, hn, hlc, hc40, hlv, hke, hfr⟩ := hr
  refine ⟨⟨hc40, hlv, fun hc => ?_⟩, hlc, hv, hn⟩
  rcases Nat.lt_or_ge cd need with hlt | hge
  · obtain ⟨hin, hap⟩ := hfr hlt hc
    exact ⟨Or.inr ⟨hin, fun r hr => hap r (h.le.mem_old hr)⟩,
      ob_fresh h.sok (WC.cap0 hP h) hin hap (hlv hc).2.1 hrs hc⟩
  · obtain ⟨rfl, rfl⟩ := hke hge
    obtain ⟨l1, o1⟩ := hd.2.2 hc
    exact ⟨l1, o1.back hx hsb.1⟩

set_option maxRecDepth 20000 in
/-- a live local through `stk.nat` (no destination; level up; array kept or fresh) -/
theorem LN.stkN (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M M' : Memory}
    {L1 L2 : List (Nat × Nat)} {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x70)
    (hF : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 (stkWs M st)) (hx : LiveExt R L1 L2) (hlc : stLen M st ≤ stCap M st)
    (hl : stLen M st ≤ stLen M' st)
    (harr : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L1))
    {q l c v : Nat} (hq : LN R L s.mem st M L1 q l c v) : LN R L s.mem st M' L2 q l c v := by
  have hk := hP.kf
  have hF0 : MemFrame M M' (R.rt ++ [(sp - 8 - stk, sp - 8 + above)] ++ [] ++ stkWs M st) := by
    simpa only [List.append_nil] using hF
  have hL0 : LiveFrame M M' L1 ([] ++ stkWs M st) := by simpa only [List.nil_append] using hLF
  refine hq.keep hx hF.accessible (fun c0 a k h1 h2 => ?_) (fun c0 => ((hq.1.2.2 c0).2).mono hx hl harr)
  obtain ⟨w1, w2, -, -, -⟩ := Loc.ap hP (hq.1.2.2 c0).1
  have hob := (hq.1.2.2 c0).2
  have hout := hob.out hlc w2
  unfold Apart at w1
  simp only [stkWs, outside_cons, outside_nil, and_true] at hout
  refine keepH (cw := [(sp - 8 - stk, sp - 8 + above)]) hF0 hL0 (hob.1.sub h1 h2) ?_
    (by simp only [outside_nil]) ?_
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, outside_cons, outside_nil, and_true]; omega

end

/-- a callee that does not touch the stack: the frame in the `stepC` form and `StackBackL` (array and length kept) -/
theorem nonStk {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {cw : List (Nat × Nat)}
    {pd cd : Nat} (hok : StkOK M R L1 st) (hx : LiveExt R L1 L2)
    (hF : MemFrame M M' (R.rt ++ cw ++ [(pd, pd + 8 * cd)])) (hLF : LiveFrame M M' L1 [(pd, pd + 8 * cd)])
    (h1 : Outside st 24 cw) (h2 : Outside st 24 [(pd, pd + 8 * cd)]) :
    MemFrame M M' (R.rt ++ cw ++ [(pd, pd + 8 * cd)] ++ stkWs M st) ∧
      LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ stkWs M st) ∧ StackBackL R L1 L2 st M M' ∧
      (stW M' st = stW M st ∧ stCap M' st = stCap M st) := by
  have hF0 : MemFrame M M' (R.rt ++ cw ++ [(pd, pd + 8 * cd)] ++ []) := by simpa only [List.append_nil] using hF
  have hL0 : LiveFrame M M' L1 ([(pd, pd + 8 * cd)] ++ []) := by simpa only [List.append_nil] using hLF
  have hhd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    keepH hF0 hL0 (hok.2.1.sub (by omega) (by omega)) (h1.of_sub (by omega) (by omega))
      (h2.of_sub (by omega) (by omega)) (by simp only [outside_nil])
  have e0 : stW M' st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen M' st = stLen M st := hhd 8 (by omega)
  have e2 : stCap M' st = stCap M st := hhd 16 (by omega)
  refine ⟨hF.mono fun a k ho => by rw [outside_append] at ho; exact ho.1,
    Expmc.liveFrame_widen hLF fun a k ho => by rw [outside_append] at ho; exact ho.1,
    ⟨⟨stkOK_hdr hok hF e0 e1 e2 hx, e1, Or.inl ⟨e0, e2⟩⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩, e0, e2⟩

section
variable {R : RtInv} {L : List (Nat × Nat)} {K g sp st zp zc : Nat} {m0 : Memory}

/-- a scratch nat of `stk.nat` (at level `ℓb`, now level `ℓ ≥ ℓb + k`) is a destination -/
theorem DL.of_scr {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc m0 M L1 b1 ℓ)
    {p k ℓb : Nat} (hs : Scr R L L1 m0 M st p k) (hp : p = stW M st + 8 * ℓb) (hl : ℓb + k ≤ ℓ)
    (hk : k < 2 ^ 40) : DL R L m0 st M L1 p k := by
  have hlen := h.len
  exact ⟨hk, fun _ => ⟨hs.al, hs.held, hs.acc, hs.b48⟩, fun _ => ⟨hs.loc, hs.held, Or.inl ⟨by omega, by omega⟩⟩⟩

/-- a new scratch nat (relative to the call memory `M`, live set `L1`) is apart from every live local of `M` -/
theorem Scr.apartLN {M M' : Memory} {L1 L2 : List (Nat × Nat)} {t k : Nat} (hs : Scr R L1 L2 M M' st t k)
    (hlc : stLen M st ≤ stCap M st) {q l c v : Nat} (hq : LN R L m0 st M L1 q l c v) (hc : 0 < c) :
    Apart t (8 * k) q (8 * c) := by
  have hob := (hq.1.2.2 hc).2
  exact hs.apart hob.1 fun _ => hob.free hlc

end

/-! ## The context after the entry -/

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the context after the function's own entry writes (frame `EvEnt.FW sp`, `EvEnt.entA`) at the entry level -/
theorem wc_init (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M [(sp + 0x1a8, sp + 0x1b0), (sp + 0x1e8, sp + 0x220)])
    (hrg : M.regions = s.mem.regions) :
    WC R L K g sp st zp zc s.mem M L b (stLen s.mem st) := by
  have hk := hP.kf
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  obtain ⟨hstw, -⟩ := hP.stkF
  have hsok := hP.stk0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hinv⟩ := hP
  unfold Apart at hstw
  have hFW : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st s.mem) →
      Outside a k [(sp + 0x1a8, sp + 0x1b0), (sp + 0x1e8, sp + 0x220)] := by
    intro a k ho
    simp only [WN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have hhd : Outside st 24 [(sp + 0x1a8, sp + 0x1b0), (sp + 0x1e8, sp + 0x220)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have e0 : stW M st = stW s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M st = stLen s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M st = stCap s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  refine ⟨hF.mono fun a k ho => hFW a k ho, LiveFrame.of_win hF (fun r hr => by
      have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega), hrg,
    LiveExt.refl R L, Expmc.inv_frame hF ?_ hinv, stkOK_hdr hsok hF e0 e1 e2 (LiveExt.refl R L), e1, Nat.le_refl _,
    hsok.2.2.2.2.2.1, Or.inl ⟨e0, e2⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩
  intro r hr
  right
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> exact hout.of_sub (by omega) (by omega)

end

end FvModexp.Amd64.ExpSlow
