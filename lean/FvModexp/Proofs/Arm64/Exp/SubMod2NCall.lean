import FvModexp.Proofs.Arm64.Exp.SubMod2NSeg

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

theorem sub_names : ∀ x, NatSub.names.contains x = true → LibExp.names.contains x = true :=
  sub_of_all (by decide)

theorem add_names : ∀ x, NatAdd.names.contains x = true → LibExp.names.contains x = true :=
  sub_of_all (by decide)

set_option maxRecDepth 20000 in
/-- a call of `nat.sub` (premise `SubHypR`) at its entry `1781872`, continuation form -/
theorem subCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} (hsub : SubHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : BitVec 64}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatSub.names).link impl) ra) (bra : ra < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 1781872) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = zp) (h1 : S.regs 1 = zl) (h2 : S.regs 2 = zc) (h3 : S.regs 3 = xp) (h4 : S.regs 4 = xl)
    (h5 : S.regs 5 = xc) (h6 : S.regs 6 = yp) (h7 : S.regs 7 = yl) (h8 : S.regs 8 = yc)
    (hpre : NatSub.Pre R b L zp zc xp xl xc yp yl yc S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → NatSub.Post R b L zp zc xp xl yp yl S s' →
      (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) →
      (s'.regs 2).toNat < 2 ^ 40 → ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap sub_names (hsub b L zp zl zc xp xl xc yp yl yc)
  rw [show segAddr Extracted.program NatSub.fn = 1781872 by decide] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  · exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq hr1 hr2

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (premise `AddHypR`) at its entry `1781184`, continuation form -/
theorem addCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} (hadd : AddHypR impl R)
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : BitVec 64}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatAdd.names).link impl) ra) (bra : ra < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 1781184) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = zp) (h1 : S.regs 1 = zl) (h2 : S.regs 2 = zc) (h3 : S.regs 3 = xp) (h4 : S.regs 4 = xl)
    (h5 : S.regs 5 = xc) (h6 : S.regs 6 = yp) (h7 : S.regs 7 = yl) (h8 : S.regs 8 = yc)
    (hpre : NatAdd.Pre R b L zp zc xp xl xc yp yl yc S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → NatAdd.Post R b L zp zc xp xl yp yl S s' →
      (NatAdd.need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) →
      (s'.regs 2).toNat < 2 ^ 40 → ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap add_names (hadd b L zp zl zc xp xl xc yp yl yc)
  rw [show segAddr Extracted.program NatAdd.fn = 1781184 by decide] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩
  · exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq hr1 hr2

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
