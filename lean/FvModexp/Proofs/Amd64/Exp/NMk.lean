import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Amd64.Nat.WordTData
import FvModexp.Proofs.Common.BitLemmas
import Janus.Contracts.AllocSat

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): `z = z.make(len m)` (nat.go:694, nat.go:57-69), `J4` = fn+0x464 → `J5` = fn+0x56b / the
`makeslice` return points (agent expmc s68; twin of `Arm64.ExpN.mk`)

`len m ≠ 0` (`TESTQ R11` not taken); `n ≤ cap z` (`CMPQ R11, CX; JG`) → reuse: `BX := n`, `J5` (`KU`); else `st`
(`DI`) spilled to `t - 0x18`, and `makeslice(Word, 1, 1)` (`n = 1`, return fn+0x49c) or `makeslice(Word, n, n + 4)`
(`n + 4` spilled to `t - 0x90`, return fn+0x512); `KA` at the return point with the contract's raw facts (the reloads
of nat.go:699 are the next segment's). Entry `RSP = t - 0x108`, `t = sp + 0x498`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- a read of exactly the bytes just written (the addresses equal up to arithmetic) -/
theorem rdw_eq {m : Janus.Arm64.Memory} {a b n v : Nat} (h : a = b) : (m.writeLE a n v).readLE b n = v % 256 ^ n := by
  subst h; exact Janus.Arm64.Memory.readLE_writeLE_self _ _ _ _

set_option pp.deepTerms false
set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `z.make(len m)` from `J4` (`RSP = t - 0x108`, `CX = cap z`, `DI = st`, `R11 = len m`) -/
theorem mk (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibN.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Amd64.Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g fs t zc st n : Nat) (M : Janus.Arm64.Memory)
    (hce : CallW.CEnv R L g fs (t - 0x498) K 0x510 M) (hK : 4400 ≤ K) (ht : 0x498 ≤ t)
    (hty : Outside StackNat.wT 16 R.rt)
    (hzc : zc < 2 ^ 40) (hst : st < 2 ^ 64) (hn0 : 0 < n) (hn : n ≤ 2 ^ 16)
    (hok : zc < n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [StackNat.wT, n, makeCap n] ∧
      blockSize (8 * makeCap n) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6190084) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h1 : S.regs 1 = BitVec.ofNat 64 zc) (h7 : S.regs 7 = BitVec.ofNat 64 st) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hmem : S.mem = M)
    (KU : n ≤ zc → ∀ S' : State, S'.rip = BitVec.ofNat 64 6190347 → S'.regs 3 = S.regs 11 →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 4 = S.regs 4 →
      S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 8 = S.regs 8 →
      S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 → S'.regs 12 = S.regs 12 →
      S'.regs 13 = S.regs 13 → S'.regs 14 = S.regs 14 → S'.regs 15 = S.regs 15 → S'.fsBase = S.fsBase →
      S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M → Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KA : zc < n → ∀ (S' : State) (p r : Nat) (m : Janus.Arm64.Memory),
      (S'.rip = BitVec.ofNat 64 6190140 ∧ n = 1 ∨ S'.rip = BitVec.ofNat 64 6190258 ∧ n ≠ 1 ∧
        m.readLE (t - 0x90) 8 = n + 4) →
      S'.regs 4 = S.regs 4 → S'.regs 0 = BitVec.ofNat 64 p → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase →
      S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = m →
      m.readLE (t - 0x18) 8 = st →
      LiveFrame M m L [] →
      MemFrame M m (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24), (t - 0x110, t - 0x108),
        (t - 0x18, t - 0x10), (t - 0x90, t - 0x88)]) →
      m.regions = M.regions → ApartAll p r L → InRanges p r R.rt → p + r ≤ 2 ^ 48 → M.accessible p r true = true →
      p % 8 = 0 → 8 * makeCap n ≤ r → r = blockSize (8 * makeCap n) true →
      R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m) →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have hce0 := hce
  obtain ⟨hal, hK0, hA0, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have bn : (BitVec.ofNat 64 n = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  subst hmem
  by_cases hr : n ≤ zc
  · janus64_run [bn, BitVec.msb_eq_decide] until [6190347]
    refine KU hr _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | rfl
  · have hr' : zc < n := by omega
    obtain ⟨hok1, hbs⟩ := hok hr'
    janus64_run [bn, BitVec.msb_eq_decide] until [6190135, 6190253]
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [show makeCap 1 = 1 from rfl] at hok1 hbs
      have hwt : Apart StackNat.wT 16 (t - 0x498 - K) (K + 0x510) := apart_of_data hd 1 (by decide) (by decide) hwacc
      janus_eval_nat h_t : StackNat.wT
      rw [h_t] at hok1 hwt hty
      unfold Apart at hwt
      obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
      have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
          ([(t - 0x110 - 4096, t - 0x110), (t - 0x110 + 8, t - 0x110 + 8 + 24)] ++ [(t - 0x110, t - 0x110 + 8)]) := by
        intro r hr
        have := hLs r hr
        simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
        omega
      have hgA : g + 16 + 8 ≤ t - 264 - 8 - 4096 ∨ t - 264 - 8 ≤ g + 16 := by unfold Apart at hgw; omega
      have hgB : g + 16 ≤ t - 264 - 8 ∨ t - 264 - 8 + 16 ≤ g := by unfold Apart at hgw; omega
      have q1 : ((S.mem.writeLE (t - 264 + 240) 8 st).writeLE (t - 264 - 8) 8 6190140).readLE (g + 16) 8 + 4096 < t - 264 - 8 := by
        simp (disch := (unfold Apart at hgw; omega)) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; omega
      janus64_run [hws, hwp, BitVec.msb_eq_decide, q1] until [6190140] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ hpw1 _ _
      unfold Apart at hpw1
      have hwr : MemFrame S.mem ((S.mem.writeLE (t - 264 + 240) 8 st).writeLE (t - 264 - 8) 8 6190140)
          [(t - 0x110, t - 0x108), (t - 0x18, t - 0x10), (t - 0x90, t - 0x88)] := by janus_frame
      have hLw : LiveFrame S.mem ((S.mem.writeLE (t - 264 + 240) 8 st).writeLE (t - 264 - 8) 8 6190140) L [] := by
        repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
        exact LiveFrame.refl _ _ _
      have hF : MemFrame S.mem m (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24),
          (t - 0x110, t - 0x108), (t - 0x18, t - 0x10), (t - 0x90, t - 0x88)]) := by
        refine hwr.trans hMF fun a k ho => ?_
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨⟨by omega, by omega, by omega⟩, ho.1, by omega, by omega⟩
      have hout : ∀ a, t - 0x90 ≤ a → a + 8 ≤ t - 0x10 →
          Outside a 8 (R.rt ++ [(t - 264 - 8 - 4096, t - 264 - 8), (t - 264 - 8 + 8, t - 264 - 8 + 8 + 24)]) := by
        intro a h1 h2
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩
      have hrs : m.readLE (t - 0x18) 8 = st := by
        rw [hMF.readLE _ _ (hout (t - 0x18) (by omega) (by omega))]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdw_eq]; omega
      refine KA hr' _ ptr.toNat _ m ?dj ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrs (hLw.trans hLF fun _ _ h => h) hF hrg1
        hAp hIn (by omega) hacc h8 (by decide) rfl hinv'
      case dj => exact Or.inl ⟨by janus64_simp, rfl⟩
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | rfl
    · have hn1 : n ≠ 1 := by omega
      rw [show makeCap n = n + 4 by unfold makeCap; rw [if_neg hn1]] at hok1 hbs KA
      have hwt : Apart StackNat.wT 16 (t - 0x498 - K) (K + 0x510) := apart_of_data hd 1 (by decide) (by decide) hwacc
      janus_eval_nat h_t : StackNat.wT
      rw [h_t] at hok1 hwt hty
      unfold Apart at hwt
      obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
      have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
          ([(t - 0x110 - 4096, t - 0x110), (t - 0x110 + 8, t - 0x110 + 8 + 24)] ++ [(t - 0x110, t - 0x110 + 8)]) := by
        intro r hr
        have := hLs r hr
        simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
        omega
      have hgA : g + 16 + 8 ≤ t - 264 - 8 - 4096 ∨ t - 264 - 8 ≤ g + 16 := by unfold Apart at hgw; omega
      have hgB : g + 16 ≤ t - 264 - 8 ∨ t - 264 - 8 + 16 ≤ g := by unfold Apart at hgw; omega
      have q1 : (((S.mem.writeLE (t - 264 + 240) 8 st).writeLE (t - 264 + 120) 8 (n + 4)).writeLE (t - 264 - 8) 8 6190258).readLE (g + 16) 8 + 4096 < t - 264 - 8 := by
        simp (disch := (unfold Apart at hgw; omega)) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; omega
      janus64_run [hws, hwp, BitVec.msb_eq_decide, q1] until [6190258] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ hpw1 _ _
      unfold Apart at hpw1
      have hwr : MemFrame S.mem (((S.mem.writeLE (t - 264 + 240) 8 st).writeLE (t - 264 + 120) 8 (n + 4)).writeLE (t - 264 - 8) 8 6190258)
          [(t - 0x110, t - 0x108), (t - 0x18, t - 0x10), (t - 0x90, t - 0x88)] := by janus_frame
      have hLw : LiveFrame S.mem (((S.mem.writeLE (t - 264 + 240) 8 st).writeLE (t - 264 + 120) 8 (n + 4)).writeLE (t - 264 - 8) 8 6190258) L [] := by
        repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
        exact LiveFrame.refl _ _ _
      have hF : MemFrame S.mem m (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24),
          (t - 0x110, t - 0x108), (t - 0x18, t - 0x10), (t - 0x90, t - 0x88)]) := by
        refine hwr.trans hMF fun a k ho => ?_
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨⟨by omega, by omega, by omega⟩, ho.1, by omega, by omega⟩
      have hout : ∀ a, t - 0x90 ≤ a → a + 8 ≤ t - 0x10 →
          Outside a 8 (R.rt ++ [(t - 264 - 8 - 4096, t - 264 - 8), (t - 264 - 8 + 8, t - 264 - 8 + 8 + 24)]) := by
        intro a h1 h2
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩
      have hrs : m.readLE (t - 0x18) 8 = st := by
        rw [hMF.readLE _ _ (hout (t - 0x18) (by omega) (by omega))]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdw_eq]; omega
      refine KA hr' _ ptr.toNat _ m ?dj2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrs (hLw.trans hLF fun _ _ h => h) hF hrg1
        hAp hIn (by omega) hacc (h8 (Or.inr (by omega))) (Janus.Contracts.AllocSat.le_blockSize _ _) rfl hinv'
      case dj2 => exact (Or.inr ⟨by janus64_simp, hn1, by
              rw [hMF.readLE _ _ (hout (t - 0x90) (by omega) (by omega))]
              simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdw_eq]; omega⟩)
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | rfl

end FvModexp.Amd64.ExpN
