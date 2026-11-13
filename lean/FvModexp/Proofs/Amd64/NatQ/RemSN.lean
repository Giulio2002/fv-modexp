import FvModexp.Proofs.Amd64.NatQ.RemDefs
import FvModexp.Proofs.Amd64.Nat.StackNatXDefs
import FvModexp.Proofs.Amd64.Nat.DivmcCall

set_option autoImplicit false

/-!
# `nat.rem` (amd64, Q-form): the `(*stack).nat(k)` call — its precondition and what holds after it
(twin of Arm64/NatQ/RemSnPre.lean + RemSN.lean; divmc s58)

* `sn_pre`: at the callee entry `S` (`RSP = r - 208`, memory changed only in `rem`'s frame `fw s`), `RemPreQ` gives
  `StackNatX.PreQ … 4192 24 st (kq ul vl)`.
* `sn_of`: the callee's `PostQ` gives the result registers, the frame slots `Sl` and `SN` (the stack after the call,
  relative to `rem`'s entry state `s`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.NatRem

open FvModexp.Amd64.NHyp (RemPreQ)

variable {H : Nat}

set_option maxHeartbeats 4000000 in
/-- `Sl` survives a frame that leaves the slots alone -/
theorem Sl.frame {s : State} {zp zl zc st up ul uc : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Sl s zp zl zc st up ul uc M) (hF : MemFrame M M' ws)
    (hws : ∀ a n, (s.regs 4).toNat - 89 ≤ a → a + n ≤ (s.regs 4).toNat + 88 → Outside a n ws)
    (h89 : 89 ≤ (s.regs 4).toNat) : Sl s zp zl zc st up ul uc M' where
  ra := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.ra
  bp := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.bp
  dbit := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.dbit
  zp' := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.zp'
  zl' := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.zl'
  zc' := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.zc'
  dfn := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.dfn
  dst := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.dst
  dn := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.dn
  dp := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.dp
  s1 := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.s1
  s2 := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.s2
  s3 := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.s3
  s4 := (hF.readLE _ _ (hws _ _ (by omega) (by omega))).trans h.s4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sn_pre {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {zp zl zc st up ul uc vp vl vc : Nat} {s S : State}
    (hpre : RemPreQ R b H L 41720 112 zp zl zc st up ul uc vp vl vc (need ul vl) (c + stkR H s.mem st) s)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 208) (hg : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    (hF : MemFrame s.mem S.mem (fw s)) (hreg : S.mem.regions = s.mem.regions) :
    StackNatX.PreQ R b L H 4192 24 st (kq ul vl) S := by
  obtain ⟨-, hce, hsv, -, -, -, -, -, hins, hsok, hsw, -, harr, -, hneed, hwba, hwbs, hfree, -, -, -, -, hcst, -,
    hinv, -, -, -, hlv⟩ := hpre
  have hu := (hins up ul (by simp)).2.1
  have hce' := hce
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, -, -, -, -, -⟩ := hce'
  simp only [regSP] at hb'
  have hFw : MemFrame s.mem S.mem (win s 41720 112) := hF.mono fun a n ho => by
    simp only [win, fw, outside_cons, outside_nil, and_true] at ho ⊢; omega
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 208 ∨ (s.regs 4).toNat + 88 ≤ a) →
      S.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [fw, outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hF.accessible a n v
  have eW : stW S.mem st = stW s.mem st := hrd _ _ (by omega)
  have eL : stLen S.mem st = stLen s.mem st := hrd _ _ (by omega)
  have eC : stCap S.mem st = stCap s.mem st := hrd _ _ (by omega)
  refine ⟨hce.callee hsp hg hfs (by decide) (by decide) (by decide) hFw hreg, hsv, ?ok, ?sw, ?arr,
    by simp only [kq]; omega, by rw [eL]; simp only [need, kq] at hneed ⊢; omega, ?cost, ?inv,
    by rw [hacc]; exact hwba, hwbs, by rw [eW, eL, eC]; exact hfree⟩
  case ok =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hsok
    refine ⟨a1, a2, by rw [hacc]; exact a3, a4, ?_, by rw [eL, eC]; exact a6, by rw [eC]; exact a7⟩
    show NatLive S.mem R L (stW S.mem st) (stCap S.mem st)
    rw [eW, eC]; intro h0; obtain ⟨b1, b2, b3, b4⟩ := a5 h0; exact ⟨b1, b2, by rw [hacc]; exact b3, b4⟩
  case sw => simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  case arr =>
    rw [eW, eC, hg]; intro h0
    obtain ⟨h1, h2⟩ := harr h0
    simp only [win, outside_cons, outside_nil, and_true] at h1 ⊢
    exact ⟨by rw [hsp]; omega, h2⟩
  case cost =>
    refine ⟨by rw [eL]; simp only [need, kq] at hlv ⊢; omega, ?_⟩
    rw [stkR_congr eC]; omega
  case inv =>
    rw [hg]
    refine RtInv.inv_frame' hF (fun r hr => ?_) hinv
    simp only [fw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by simp only; omega) (by simp only; omega))

/-- the stack after `stk.nat(k)`, relative to `rem`'s entry state `s` -/
structure SN (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (st k : Nat) (s : State) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  ext : LiveExt R L L1
  bud : b - stkR H s.mem st + stkR H M st ≤ b1
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M)
  sok : StkOK M R L1 st
  len : stLen M st = stLen s.mem st + StackNat.rnd k
  kept : stLen s.mem st + StackNat.rnd k ≤ stCap s.mem st → stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  fresh : stCap s.mem st < stLen s.mem st + StackNat.rnd k →
    InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L
  arrL : stCap s.mem st < stLen s.mem st + StackNat.rnd k → (stW M st, stW M st + 8 * stCap M st) ∈ L1
  mf : MemFrame s.mem M (R.rt ++ win s 41720 112 ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L (stkWs s.mem st)
  reg : M.regions = s.mem.regions

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sn_of {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {zp zl zc st up ul uc vp vl vc : Nat} {s S T : State}
    (hpre : RemPreQ R b H L 41720 112 zp zl zc st up ul uc vp vl vc (need ul vl) (c + stkR H s.mem st) s)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 208) (hg : S.regs 14 = s.regs 14)
    (hF : MemFrame s.mem S.mem (fw s)) (hreg : S.mem.regions = s.mem.regions)
    (hSl : Sl s zp zl zc st up ul uc S.mem)
    (hTreg : T.mem.regions = S.mem.regions)
    (hQ : StackNatX.PostQ R b L H 4192 24 st (kq ul vl) S T) :
    T.fsBase = S.fsBase ∧ T.df = S.df ∧
      T.regs 0 = BitVec.ofNat 64 (stW T.mem st + 8 * stLen s.mem st) ∧
      T.regs 3 = BitVec.ofNat 64 (kq ul vl) ∧ T.regs 1 = BitVec.ofNat 64 (kq ul vl) ∧
      Sl s zp zl zc st up ul uc T.mem ∧
      ∃ (L1 : List (Nat × Nat)) (b1 : Nat), SN R b H L st (kq ul vl) s T.mem L1 b1 := by
  obtain ⟨-, hce, -, -, -, -, -, -, -, -, hsw, -, harr, hc0, -⟩ := hpre
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, hLs, -⟩ := hce
  simp only [regSP] at hb'
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 208 ∨ (s.regs 4).toNat + 88 ≤ a) →
      S.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE _ _ (by simp only [fw, outside_cons, outside_nil, and_true]; omega)
  have eW : stW S.mem st = stW s.mem st := hrd _ _ (by omega)
  have eL : stLen S.mem st = stLen s.mem st := hrd _ _ (by omega)
  have eC : stCap S.mem st = stCap s.mem st := hrd _ _ (by omega)
  have eWs : stkWs S.mem st = stkWs s.mem st := by simp only [stkWs, eW, eL, eC]
  obtain ⟨f1, f2, q0, q1, q2, L1, b1, ⟨hx, hbud, hinv⟩, hsok, hlen, hkept, hfresh, hMF, hLF, harrL⟩ := hQ
  simp only [eL, eC, eW] at hlen hkept hfresh harrL q0
  rw [stkR_congr eC] at hbud
  rw [eWs] at hMF hLF
  have hwin : ∀ a n, (s.regs 4).toNat - 41720 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → Outside a n (stkWs s.mem st) := by
    intro a n h1 h2
    simp only [stkWs, outside_cons, outside_nil, and_true]
    refine ⟨by omega, ?_⟩
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with hc | hc
    · rw [hc0 hc, hc]; omega
    · have := (harr hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hFT : MemFrame s.mem T.mem (R.rt ++ win s 41720 112 ++ stkWs s.mem st) :=
    MemFrame.trans hF hMF fun a n ho => by
      rw [outside_append, outside_append] at ho
      obtain ⟨⟨hR, hW⟩, hS⟩ := ho
      simp only [win, outside_cons, outside_nil, and_true] at hW
      refine ⟨?_, ?_⟩
      · simp only [fw, outside_cons, outside_nil, and_true]; omega
      · rw [outside_append, outside_append]
        refine ⟨⟨hR, ?_⟩, hS⟩
        simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hLFT : LiveFrame s.mem T.mem L (stkWs s.mem st) := ⟨fun a n hin ho => by
    rw [hLF.readLE a n hin ho]
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this
    exact hF.readLE _ _ (by simp only [fw, outside_cons, outside_nil, and_true]; omega)⟩
  have hsl : Sl s zp zl zc st up ul uc T.mem := hSl.frame hMF (fun a n h1 h2 => by
    rw [outside_append, outside_append]
    refine ⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, hwin a n (by omega) (by omega)⟩
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega) (by omega)
  refine ⟨f1, f2, q0 (by simp only [kq]; omega), q1, q2, hsl, L1, b1,
    ⟨hx, hbud, by rw [← hg]; exact hinv, hsok, hlen, hkept, hfresh, harrL, hFT, hLFT, ?_⟩⟩
  rw [hTreg, hreg]

end FvModexp.Amd64.Q.NatRem
