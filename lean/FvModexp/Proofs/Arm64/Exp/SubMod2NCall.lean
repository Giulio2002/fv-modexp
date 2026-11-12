import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.CallWW
import FvModexp.Proofs.Arm64.Exp.SubMod2NSeg
import FvModexp.Proofs.Arm64.Exp.CmpW

/-!
# `nat.subMod2N` (arm64): the `nat.sub` / `nat.add` call helpers (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp

theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem sub_names : ∀ x, NatSub.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)

theorem add_names : ∀ x, NatAdd.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)

set_option maxRecDepth 20000 in
/-- a call of `nat.sub` (premise `SubHypR`) at its entry `1781872` with `SP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem subCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} (hsub : SubHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat} {M : Memory}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatSub.names).link impl) ra) (bra : ra < 2 ^ 64)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' < 2 ^ 64) (bx39 : xl < 2 ^ 39)
    (hpc : S.pc = BitVec.ofNat 64 1781872) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 xp) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 sp') (h28 : (S.regs 28).toNat = g)
    (hpre : NatSub.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.pc = BitVec.ofNat 64 ra →
      s'.sp = BitVec.ofNat 64 sp' → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 → s'.regs 18 = S.regs 18 →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl - natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ xl → LiveExt R L L' → b - makeCost xl ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4304, sp' - 8), (sp' + 8, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] → (xl ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS' := CallWW.hypSum hap sub_names (hsub b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatSub.fn = 1781872 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  · obtain ⟨p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    have hspT : S.sp.toNat = sp' := by rw [hsp]; exact tN bsp
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [winA, hspT, h28] at hF hinv
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (hr.trans h30) (e1.trans hsp) e2 e3 e4 hrg (by rw [← q0, Expmc.bv_ofNat_toNat])
      (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat]) hv hn hlc hln hLE hb hinv hlive hor
      hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 bx39)
    obtain ⟨a1, a2⟩ := hr1 h
    exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (premise `AddHypR`) at its entry `1781184` with `SP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem addCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} (hadd : AddHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat} {M : Memory}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatAdd.names).link impl) ra) (bra : ra < 2 ^ 64)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' < 2 ^ 64) (bx39 : xl < 2 ^ 39) (by39 : yl < 2 ^ 39)
    (hpc : S.pc = BitVec.ofNat 64 1781184) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 xp) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (hS : S.mem = M) (hsp : S.sp = BitVec.ofNat 64 sp') (h28 : (S.regs 28).toNat = g)
    (hpre : NatAdd.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.pc = BitVec.ofNat 64 ra →
      s'.sp = BitVec.ofNat 64 sp' → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 → s'.regs 18 = S.regs 18 →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl + natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ max xl yl + 1 → LiveExt R L L' →
      b - makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4464, sp' - 8), (sp' + 8, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] →
      ((if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 →
      p' < 2 ^ 64 ∧ n' < 2 ^ 64 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS' := CallWW.hypSum hap add_names (hadd b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatAdd.fn = 1781184 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  · obtain ⟨p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    have hspT : S.sp.toNat = sp' := by rw [hsp]; exact tN bsp
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [winA, hspT, h28] at hF hinv
    simp only [NatAdd.mx, NatAdd.need, tN bxl, tN byl] at hln hb hr1 hr2
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (hr.trans h30) (e1.trans hsp) e2 e3 e4 hrg (by rw [← q0, Expmc.bv_ofNat_toNat])
      (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat]) hv hn hlc hln hLE hb hinv hlive hor
      hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 (by omega)) ⟨by rw [← q0]; exact BitVec.isLt _, by rw [← q1]; exact BitVec.isLt _⟩
    obtain ⟨a1, a2⟩ := hr1 h
    exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

/-- a call of `nat.cmp` (asm's `cmp_summary`) at its entry, `ReachesRet` continuation form -/
theorem cmpCall {impl : List Segment} {S : State} {ret : BitVec 64} {Q : State → Prop}
    (hpc : S.pc = BitVec.ofNat 64 1782608) (hpre : CmpSum.Pre S)
    (K : ∀ S' : State, S'.pc = S.regs 30 → S'.sp = S.sp →
      S'.regs 0 = CmpSum.cmpRes (S.regs 1).toNat (S.regs 4).toNat (S.mem.readLE (S.regs 0).toNat (8 * (S.regs 1).toNat))
        (S.mem.readLE (S.regs 3).toNat (8 * (S.regs 4).toNat)) →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      MemFrame S.mem S'.mem [(S.sp.toNat - 24, S.sp.toNat - 8), (S.sp.toNat + 8, S.sp.toNat + 16),
        (S.sp.toNat + 32, S.sp.toNat + 40)] → S'.mem.regions = S.mem.regions →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  refine ReachesRet.call_regions (LibWC.cmpSum impl) hpc hpre fun s' hr hq hrg => ?_
  obtain ⟨v1, v2, v4, v5, v16, f, m, rfl, hf⟩ := hq
  exact K _ hr rfl (by simp [setReg]; rfl) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) hf hrg

/-- the frame words survive a callee at `SP - 144` -/
theorem fw_call {R : RtInv} {s : State} {M M' : Memory} {zp zl zc yp n stk above : Nat} {zr : Nat × Nat}
    (hs : 4608 ≤ s.sp.toNat) (hout : Outside (s.sp.toNat - 4608) (4608 + 88) R.rt)
    (hzw : zp + 8 * zc ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 88 ≤ zp) (hzr : zr = (zp, zp + 8 * zc) ∨ zr.2 = 0)
    (hk : stk ≤ 4464) (ha : above ≤ 88) (h : Fw s M zp zl zc yp n)
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 144 - stk, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + above)] ++ [zr])) : Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 88 → (a + 8 ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 56 ≤ a) →
      M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
    rcases hzr with rfl | h0
    · simp only [outside_cons, outside_nil, and_true]; omega
    · obtain ⟨z1, z2⟩ := zr
      simp only at h0; subst h0
      simp only [outside_cons, outside_nil, and_true]; omega
  exact ⟨(r _ (by omega) (by omega) (by omega)).trans f1, (r _ (by omega) (by omega) (by omega)).trans f2,
    (r _ (by omega) (by omega) (by omega)).trans f3, (r _ (by omega) (by omega) (by omega)).trans f4,
    (r _ (by omega) (by omega) (by omega)).trans f5, (r _ (by omega) (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega) (by omega)).trans f7⟩

/-- `nat.cmp`'s frame at `SP - 144` lies in the function's `winA` and in the generic callee frame -/
theorem cmp_frame {R : RtInv} {s S : State} {M M' : Memory} (hs : 4608 ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - 144)
    (hF : MemFrame M M' [(S.sp.toNat - 24, S.sp.toNat - 8), (S.sp.toNat + 8, S.sp.toNat + 16),
        (S.sp.toNat + 32, S.sp.toNat + 40)]) :
    MemFrame M M' (winA s K A) ∧ MemFrame M M' (R.rt ++ [(s.sp.toNat - 144 - 24, s.sp.toNat - 144 - 8),
      (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 40)] ++ [((0 : Nat), (0 : Nat))]) := by
  rw [hsp] at hF
  refine ⟨hF.mono fun a n h => ?_, hF.mono fun a n h => ?_⟩
  · simp only [winA, K, A, outside_cons, outside_nil, and_true] at h ⊢; omega
  · simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxRecDepth 20000 in
/-- the precondition of `z.sub(x, y)` at `SP - 144` (`z`'s array reused: `len x ≤ ⌈n/64⌉ ≤ cap z`) -/
theorem subPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) {S : State} (hS : S.mem = M)
    (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {xp xl xc yp' yl' yc' : Nat} (hyx : yl' ≤ xl) (hYX : natVal M yp' yl' ≤ natVal M xp xl) (hxc : xl ≤ xc)
    (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40) (hxW : xl ≤ W n)
    (hzx : zp = xp ∨ Apart zp (8 * zc) xp (8 * xl)) (hzy : zp = yp' ∨ Apart zp (8 * zc) yp' (8 * yl'))
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxh : Held R L1 xp (8 * xl))
    (hxn : NatNorm M xp xl) (hxw : xp + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ xp)
    (hya : M.accessible yp' (8 * yl') false = true) (hy48 : yp' + 8 * yl' ≤ 2 ^ 48) (hyh : Held R L1 yp' (8 * yl'))
    (hyn : NatNorm M yp' yl') (hyw : yp' + 8 * yl' ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ yp') :
    NatSub.Pre R b1 L1 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hce := CallW.callEnv_of (cenv_of hpre hrt (dl_of hpre hrt)) hsp (h28.trans (Expmc.bv_ofNat_toNat _).symm) hS
    (show 4304 ≤ 4464 by omega) (show 80 ≤ 88 by omega)
  have hsp4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hW := hpre.2.2.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by simp only [W] at hW; omega)).2.2.2
  have hserv := hpre.2.1
  have hwt := hpre.2.2.1
  obtain ⟨-, -, -, -, -, hinv, hlive⟩ := hrt
  simp only [W] at hW hxW
  have hxp : xp < 2 ^ 64 := by omega
  have hyp : yp' < 2 ^ 64 := by omega
  unfold NatSub.Pre NatSub.PreS
  rw [tN (show zp < 2 ^ 64 by omega), tN (show zc < 2 ^ 64 by omega), tN hxp, tN (show xl < 2 ^ 64 by omega),
    tN (show xc < 2 ^ 64 by omega), tN hyp, tN (show yl' < 2 ^ 64 by omega), tN (show yc' < 2 ^ 64 by omega), hS]
  simp only [win, hspT, h28, K, A, outside_cons, outside_nil, and_true] at hzw ⊢
  refine ⟨hce, hwt, hyx, hYX, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc, hlive, by omega,
    fun _ => ⟨by unfold Apart at hzg ⊢; omega, ?_, ?_⟩, hxa, hx48, hxh, hxn, hyn, by omega, hya, hy48, hyh, by omega, hinv,
    fun h => absurd h (by omega), fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h

end FvModexp.Arm64.SubMod2N

namespace FvModexp.Arm64.SubMod2N

set_option maxRecDepth 20000 in
/-- the precondition of `z.add(x, y)` at `SP - 144` (`len x, len y ≤ ⌈n/64⌉`; at most `k ≤ 4` budgeted calls before) -/
theorem addPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State} (hS : S.mem = M)
    (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h28 : S.regs 28 = s.regs 28)
    {xp xl xc yp' yl' yc' : Nat} (hxc : xl ≤ xc) (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40)
    (hxW : xl ≤ W n) (hyW : yl' ≤ W n)
    (hzx : zp = xp ∨ Apart zp (8 * zc) xp (8 * xl)) (hzy : zp = yp' ∨ Apart zp (8 * zc) yp' (8 * yl'))
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxh : Held R L1 xp (8 * xl))
    (hxn : NatNorm M xp xl) (hxw : xp + 8 * xl ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ xp)
    (hya : M.accessible yp' (8 * yl') false = true) (hy48 : yp' + 8 * yl' ≤ 2 ^ 48) (hyh : Held R L1 yp' (8 * yl'))
    (hyn : NatNorm M yp' yl') (hyw : yp' + 8 * yl' ≤ s.sp.toNat - 4608 ∨ s.sp.toNat - 56 ≤ yp') :
    NatAdd.Pre R b1 L1 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hce := CallW.callEnv_of (cenv_of hpre hrt (dl_of hpre hrt)) hsp (h28.trans (Expmc.bv_ofNat_toNat _).symm) hS
    (show 4464 ≤ 4464 by omega) (show 80 ≤ 88 by omega)
  have hsp4 : 4608 ≤ s.sp.toNat := hpre.1.2.1.2.1
  have hspT : S.sp.toNat = s.sp.toNat - 144 := by rw [hsp]; exact tN (by omega)
  have hW := hpre.2.2.2.2.2.2.2.2.2.1
  have hn2 := hpre.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by simp only [W] at hW; omega)).2.2.2
  have hcost := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hserv := hpre.2.1
  have hwt := hpre.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, hlive⟩ := hrt
  have hmk : makeCost (if min xl yl' = 0 then max xl yl' else max xl yl' + 1) ≤ wCost n :=
    makeCost_le_w (by split <;> omega)
  simp only [W] at hW hxW hyW
  simp only [cost] at hcost
  have hkw : k * wCost n ≤ 4 * wCost n := Nat.mul_le_mul_right _ hk
  have hxp : xp < 2 ^ 64 := by omega
  have hyp : yp' < 2 ^ 64 := by omega
  unfold NatAdd.Pre NatAdd.PreS
  simp only [NatAdd.need, NatAdd.mx]
  rw [tN (show zp < 2 ^ 64 by omega), tN (show zc < 2 ^ 64 by omega), tN hxp, tN (show xl < 2 ^ 64 by omega),
    tN (show xc < 2 ^ 64 by omega), tN hyp, tN (show yl' < 2 ^ 64 by omega), tN (show yc' < 2 ^ 64 by omega), hS]
  simp only [win, hspT, h28, K, A, outside_cons, outside_nil, and_true] at hzw ⊢
  refine ⟨hce, hwt, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc, hlive, by omega,
    fun _ => ⟨by unfold Apart at hzg ⊢; omega, ?_, ?_⟩, hxa, hx48, hxh, hxn, hyn, by omega, hya, hy48, hyh, by omega, hinv,
    fun _ => ⟨hserv.1 _ _ _ (by unfold makeCap; split <;> split <;> omega), by omega⟩,
    fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h

end FvModexp.Arm64.SubMod2N
