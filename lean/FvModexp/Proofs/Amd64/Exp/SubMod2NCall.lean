import FvModexp.Proofs.Amd64.Exp.SubMod2NSeg

/-!
# `nat.subMod2N` (amd64): the `nat.sub` / `nat.add` / `nat.cmp` call helpers (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

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
/-- a call of `nat.sub` (premise `SubHypR`) at its entry `6183136` with `RSP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem subCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hsub : SubHypR impl R) {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat}
    {M : Memory} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatSub.names).link impl) ra)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' + 8 < 2 ^ 64) (bx39 : xl < 2 ^ 39)
    (hpc : S.rip = BitVec.ofNat 64 6183136) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = sp') (h14 : (S.regs 14).toNat = g)
    (hpre : NatSub.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 ra →
      s'.regs 4 = BitVec.ofNat 64 (sp' + 8) → s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      s'.fsBase = S.fsBase → s'.df = S.df →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl - natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ xl → LiveExt R L L' → b - makeCost xl ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4288, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] → (xl ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS' := CallW.hypSum hap sub_names (by simp [numIntRegs])
    (hsub b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatSub.fn = 6183136 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hpre⟩
    fun s' hr ⟨⟨e1, _, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  · obtain ⟨hfs, hdf', p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [win, hsp, h14] at hF hinv
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (by rw [hr, retAddrOf_eq, hrd]) ?_ e3 e4 hfs hdf' hrg
      (by rw [← q0, Expmc.bv_ofNat_toNat]) (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat])
      hv hn hlc hln hLE hb hinv hlive hor (by simpa only [show 4288 + 80 = 4368 from rfl] using hF) hLF
      (fun h => ?_) (by rw [← q2]; exact hr2 bx39)
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (premise `AddHypR`) at its entry `6182240` with `RSP = sp'` -/
theorem addCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hadd : AddHypR impl R) {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat}
    {M : Memory} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatAdd.names).link impl) ra)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' + 8 < 2 ^ 64) (bx39 : xl < 2 ^ 39) (by39 : yl < 2 ^ 39)
    (hpc : S.rip = BitVec.ofNat 64 6182240) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = sp') (h14 : (S.regs 14).toNat = g)
    (hpre : NatAdd.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 ra →
      s'.regs 4 = BitVec.ofNat 64 (sp' + 8) → s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      s'.fsBase = S.fsBase → s'.df = S.df →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl + natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ max xl yl + 1 → LiveExt R L L' →
      b - makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4440, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] →
      ((if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS' := CallW.hypSum hap add_names (by simp [numIntRegs])
    (hadd b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatAdd.fn = 6182240 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hpre⟩
    fun s' hr ⟨⟨e1, _, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  · obtain ⟨hfs, hdf', p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [win, hsp, h14] at hF hinv
    simp only [NatAdd.mx, NatAdd.need, tN bxl, tN byl] at hln hb hr1 hr2
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (by rw [hr, retAddrOf_eq, hrd]) ?_ e3 e4 hfs hdf' hrg
      (by rw [← q0, Expmc.bv_ofNat_toNat]) (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat])
      hv hn hlc hln hLE hb hinv hlive hor hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 (by omega))
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

/-- `CmpSum.Pre` from Nat-level facts (amd64: `x = (RAX, RBX)`, `y = (RDI, RSI)`) -/
theorem cmpPre_of {S : State} {sp x xl y yl : Nat} (hsp : (S.regs 4).toNat = sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 x) (h3 : S.regs 3 = BitVec.ofNat 64 xl)
    (h7 : S.regs 7 = BitVec.ofNat 64 y) (h6 : S.regs 6 = BitVec.ofNat 64 yl)
    (hra : S.mem.readLE sp 8 < 2 ^ 47) (h8 : 8 ≤ sp) (hsp48 : sp + 40 ≤ 2 ^ 48)
    (hacc : S.mem.accessible (sp - 8) 48 true = true)
    (hx : xl = 0 ∨ (x + 8 * xl ≤ 2 ^ 48 ∧ S.mem.accessible x (8 * xl) false = true ∧ Apart x (8 * xl) (sp - 8) 48))
    (hy : yl = 0 ∨ (y + 8 * yl ≤ 2 ^ 48 ∧ S.mem.accessible y (8 * yl) false = true ∧ Apart y (8 * yl) (sp - 8) 48)) :
    CmpSum.Pre S := by
  unfold CmpSum.Pre CmpSum.SliceOK
  rw [hsp, h0, h3, h7, h6]
  refine ⟨hra, h8, hsp48, hacc, ?_, ?_⟩
  · rcases hx with h | ⟨h1, h2, h3⟩
    · left; subst h; rfl
    · rw [tN (by omega), tN (by omega)]; exact Or.inr ⟨h2, h3⟩
  · rcases hy with h | ⟨h1, h2, h3⟩
    · left; subst h; rfl
    · rw [tN (by omega), tN (by omega)]; exact Or.inr ⟨h2, h3⟩

/-- the frame words survive a callee at `RSP_c = e - 136` -/
theorem fw_call {R : RtInv} {s : State} {M M' : Memory} {zp zl zc yp n stk above : Nat} {zr : Nat × Nat}
    (hs : 4576 ≤ (s.regs 4).toNat) (hout : Outside ((s.regs 4).toNat - 4576) (4576 + 88) R.rt)
    (hzw : zp + 8 * zc ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ zp) (hzr : zr = (zp, zp + 8 * zc) ∨ zr.2 = 0)
    (hk : stk ≤ 4440) (ha : above ≤ 80) (h : Fw s M zp zl zc yp n)
    (hF : MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 136 - stk, (s.regs 4).toNat - 136 + above)] ++ [zr])) :
    Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (s.regs 4).toNat - 8 ≤ a → a + 8 ≤ (s.regs 4).toNat + 88 → M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, ?_⟩
    rcases hzr with rfl | h0
    · simp only [outside_cons, outside_nil, and_true]; omega
    · obtain ⟨z1, z2⟩ := zr
      simp only at h0; subst h0
      simp only [outside_cons, outside_nil, and_true]; omega
  exact ⟨(r _ (by omega) (by omega)).trans f1, (r _ (by omega) (by omega)).trans f2,
    (r _ (by omega) (by omega)).trans f3, (r _ (by omega) (by omega)).trans f4,
    (r _ (by omega) (by omega)).trans f5, (r _ (by omega) (by omega)).trans f6,
    (r _ (by omega) (by omega)).trans f7⟩

/-- `nat.cmp`'s frame at `RSP_c = e - 136` lies in the function's `win` and in the generic callee frame -/
theorem cmp_frame {R : RtInv} {s S : State} {M M' : Memory} (hs : 4576 ≤ (s.regs 4).toNat)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (hF : MemFrame M M' (CmpSum.frame S)) :
    MemFrame M M' (win s K A) ∧ MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 136 - 8,
      (s.regs 4).toNat - 136 + 40)] ++ [((0 : Nat), (0 : Nat))]) := by
  unfold CmpSum.frame at hF
  rw [hsp] at hF
  refine ⟨hF.mono fun a n h => ?_, hF.mono fun a n h => ?_⟩
  · simp only [win, K, A, outside_cons, outside_nil, and_true] at h ⊢; omega
  · simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxRecDepth 20000 in
/-- the precondition of `z.sub(x, y)` at `RSP_c = e - 136` (`z`'s array reused: `len x ≤ ⌈n/64⌉ ≤ cap z`) -/
theorem subPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) {S : State} (hS : S.mem = M)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    {xp xl xc yp' yl' yc' : Nat} (hyx : yl' ≤ xl) (hYX : natVal M yp' yl' ≤ natVal M xp xl) (hxc : xl ≤ xc)
    (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40) (hxW : xl ≤ W n)
    (hzx : zp = xp ∨ Apart zp (8 * zc) xp (8 * xl)) (hzy : zp = yp' ∨ Apart zp (8 * zc) yp' (8 * yl'))
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxh : Held R L1 xp (8 * xl))
    (hxn : NatNorm M xp xl) (hxw : xp + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ xp)
    (hya : M.accessible yp' (8 * yl') false = true) (hy48 : yp' + 8 * yl' ≤ 2 ^ 48) (hyh : Held R L1 yp' (8 * yl'))
    (hyn : NatNorm M yp' yl') (hyw : yp' + 8 * yl' ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ yp') :
    NatSub.Pre R b1 L1 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hsp4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hce := CallW.callEnv_of (cenv_of hpre hrt (dl_of hpre hrt)) hsp (by rw [h14]) (by rw [hfs]) hS
    (show 4288 ≤ 4440 by omega) (show 80 ≤ 80 by omega) (by omega)
  have hW := hpre.2.2.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzf := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
  simp only [win, hsp, h14, hfs, K, A, outside_cons, outside_nil, and_true] at hzw ⊢
  refine ⟨hce, hwt, hyx, hYX, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc, hlive, by omega,
    fun _ => ⟨by unfold Apart at hzg ⊢; omega, hzf, ?_, ?_⟩, hxa, hx48, hxh, hxn, hyn, by omega, hya, hy48, hyh, by omega,
    hinv, fun h => absurd h (by omega), fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h

end FvModexp.Amd64.SubMod2N

namespace FvModexp.Amd64.SubMod2N

set_option maxRecDepth 20000 in
/-- the precondition of `z.add(x, y)` at `RSP_c = e - 136` (`len x, len y ≤ ⌈n/64⌉`; at most `k ≤ 4` budgeted calls
before) -/
theorem addPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State} (hS : S.mem = M)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    {xp xl xc yp' yl' yc' : Nat} (hxc : xl ≤ xc) (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40)
    (hxW : xl ≤ W n) (hyW : yl' ≤ W n)
    (hzx : zp = xp ∨ Apart zp (8 * zc) xp (8 * xl)) (hzy : zp = yp' ∨ Apart zp (8 * zc) yp' (8 * yl'))
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxh : Held R L1 xp (8 * xl))
    (hxn : NatNorm M xp xl) (hxw : xp + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ xp)
    (hya : M.accessible yp' (8 * yl') false = true) (hy48 : yp' + 8 * yl' ≤ 2 ^ 48) (hyh : Held R L1 yp' (8 * yl'))
    (hyn : NatNorm M yp' yl') (hyw : yp' + 8 * yl' ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ yp') :
    NatAdd.Pre R b1 L1 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hsp4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hce := CallW.callEnv_of (cenv_of hpre hrt (dl_of hpre hrt)) hsp (by rw [h14]) (by rw [hfs]) hS
    (show 4440 ≤ 4440 by omega) (show 80 ≤ 80 by omega) (by omega)
  have hW := hpre.2.2.2.2.2.2.2.2.2.1
  have hn2 := hpre.2.2.2.2.2.2.2.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzf := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
  simp only [win, hsp, h14, hfs, K, A, outside_cons, outside_nil, and_true] at hzw ⊢
  refine ⟨hce, hwt, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc, hlive, by omega,
    fun _ => ⟨by unfold Apart at hzg ⊢; omega, hzf, ?_, ?_⟩, hxa, hx48, hxh, hxn, hyn, by omega, hya, hy48, hyh, by omega,
    hinv, fun _ => ⟨hserv.1 _ _ _ (by unfold makeCap; split <;> split <;> omega), by omega⟩,
    fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h

end FvModexp.Amd64.SubMod2N
