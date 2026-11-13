import FvModexp.Proofs.Arm64.NatQ.RemDefs

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/RemSN.lean, TIGHT COSTS, asm s38)
# `nat.rem` (arm64): the state after `q := stk.nat(k)` relative to `rem`'s entry (pure)

`SN R b H L st k s M L1 b1`: `stk.nat`'s `PostL` (call state `P`, one frame below `s`) restated against the entry state `s`
(the header reads at `P` equal those at `s`; the frame `s → P` is `rem`'s own frame `fw s`): live set `L1`, budget `b1`,
the stack `(stW, stLen + rnd k, ·)` kept or freshly grown (then in `R.rt`, apart from `L`, an element of `L1`), and the
combined frame `s.mem → M` (`R.rt ++ winA s 41712 112 ++ stkWs s.mem st`, live frame outside `stkWs`).
`sn_of`: from `Pre`, `AtNat` and the `PostL` handed on by `natc`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.NatRem
open FvModexp.Arm64.NatRem
variable {H : Nat}

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

structure SN (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (st k : Nat) (s : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  ext : LiveExt R L L1
  bud : b - stkR H s.mem st + stkR H M st ≤ b1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M)
  sok : StkOK M R L1 st
  len : stLen M st = stLen s.mem st + StackNat.rnd k
  kept : stLen s.mem st + StackNat.rnd k ≤ stCap s.mem st → stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  fresh : stCap s.mem st < stLen s.mem st + StackNat.rnd k →
    InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L
  arrL : stCap s.mem st < stLen s.mem st + StackNat.rnd k → (stW M st, stW M st + 8 * stCap M st) ∈ L1
  mf : MemFrame s.mem M (R.rt ++ winA s 41712 112 ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L (stkWs s.mem st)
  reg : M.regions = s.mem.regions

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sn_of {R : RtInv} {b : Nat} {cd : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st up ul uc vp vl vc : Nat} {s P T : State}
    (hpre : Pre R b H cd L zp zl zc st up ul uc vp vl s) (hP : AtNat s P zp zl zc st up ul uc vp vl vc)
    (hTsp : T.sp = P.sp) (hT28 : T.regs 28 = P.regs 28) (hTreg : T.mem.regions = P.mem.regions)
    (hQ : StackNatX.PostQ R b L H 4208 24 st (kq ul vl) P T) :
    T.regs 0 = BitVec.ofNat 64 (stW T.mem st + 8 * stLen s.mem st) ∧
      T.regs 1 = BitVec.ofNat 64 (kq ul vl) ∧ T.regs 2 = BitVec.ofNat 64 (kq ul vl) ∧
      Sl s zp zl zc st up ul uc vp vl vc T.mem ∧
      ∃ (L1 : List (Nat × Nat)) (b1 : Nat), SN R b H L st (kq ul vl) s T.mem L1 b1 := by
  obtain ⟨⟨⟨hce, -, -, -, -, -, -, -, -, hsw, -, harr, hc0, -, -, -, -, -, -, -, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  have hsp : P.sp.toNat = s.sp.toNat - 208 := by
    rw [hP.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF := hP.fr
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 88 ≤ a) → P.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [fw, outside_cons, outside_nil, and_true]; omega)
  have eW : stW P.mem st = stW s.mem st := hrd _ _ (by omega)
  have eL : stLen P.mem st = stLen s.mem st := hrd _ _ (by omega)
  have eC : stCap P.mem st = stCap s.mem st := hrd _ _ (by omega)
  have eWs : stkWs P.mem st = stkWs s.mem st := by simp only [stkWs, eW, eL, eC]
  obtain ⟨q0, q1, q2, L1, b1, ⟨hx, hbud, hinv⟩, hsok, hlen, hkept, hfresh, hMF, hLF, harrL⟩ := hQ
  simp only [eL, eC, eW] at hlen hkept hfresh harrL q0
  rw [stkR_congr eC] at hbud
  rw [eWs] at hMF hLF
  -- the array (when `cap > 0`) and the header are outside the window
  have hwin : ∀ a n, s.sp.toNat - 41712 ≤ a → a + n ≤ s.sp.toNat + 112 → Outside a n (stkWs s.mem st) := by
    intro a n h1 h2
    simp only [stkWs, outside_cons, outside_nil, and_true]
    refine ⟨by omega, ?_⟩
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with hc | hc
    · rw [hc0 hc, hc]; omega
    · have := (harr hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hFT : MemFrame s.mem T.mem (R.rt ++ winA s 41712 112 ++ stkWs s.mem st) :=
    MemFrame.trans hF hMF fun a n ho => by
      rw [outside_append, outside_append] at ho
      obtain ⟨⟨hR, hW⟩, hS⟩ := ho
      simp only [winA, outside_cons, outside_nil, and_true] at hW
      refine ⟨?_, ?_⟩
      · simp only [fw, outside_cons, outside_nil, and_true]; omega
      · rw [outside_append, outside_append]
        refine ⟨⟨hR, ?_⟩, hS⟩
        simp only [winA, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hLFT : LiveFrame s.mem T.mem L (stkWs s.mem st) := ⟨fun a n hin ho => by
    rw [hLF.readLE a n hin ho]
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this
    exact hF.readLE _ _ (by simp only [fw, outside_cons, outside_nil, and_true]; omega)⟩
  have hsl : Sl s zp zl zc st up ul uc vp vl vc T.mem := hP.sl.frame hMF (fun a n h => by
    rw [outside_append, outside_append]
    refine ⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, hwin a n (by omega) (by omega)⟩
    simp only [winA, outside_cons, outside_nil, and_true]; rw [hsp]; omega) (by omega)
  refine ⟨q0 (by simp only [kq]; omega), q1, q2, hsl, L1, b1,
    ⟨hx, hbud, by rw [← hP.r28]; exact hinv, hsok, hlen, hkept, hfresh, harrL, hFT, hLFT, ?_⟩⟩
  rw [hTreg, hP.reg]

end FvModexp.Arm64.Q.NatRem
