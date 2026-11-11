import FvModexp.Proofs.Amd64.Exp.SubMod2NSeg2

/-!
# `nat.subMod2N` (amd64): `J5` → return: `z = z.trunc(z, n)`, `return z.add(z, natOne)` (nat.go:1754-1755) (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-- name the memory of a symbolic state -/
theorem memAbs {M M2 : Memory} {rs : List (Nat × Nat)} (_h : MemFrame M M2 rs) : ∃ Mx, Mx = M := ⟨M, rfl⟩

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (premise `AddHypR`) at its entry `6182240` with `RSP = sp'` -/
theorem addCallB {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
      ((if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 → p' < 2 ^ 64 →
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
      hv hn hlc hln hLE hb hinv hlive hor hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 (by omega)) (by rw [← q0]; exact BitVec.isLt _)
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

theorem natOneA_eq : natOneA = 12050400 := by decide

set_option maxRecDepth 20000 in
/-- the global `natOne` survives the function's writes -/
theorem one_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) :
    M.readLE 12050400 8 = op ∧ M.readLE 12050408 8 = 1 ∧ M.readLE 12050416 8 = 1 ∧ M.readLE op 8 = 1 ∧
      M.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L1 op 8 ∧
      (op + 8 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ op) ∧ Apart zp (8 * zc) op 8 ∧
      M.accessible 12050400 24 false = true := by
  obtain ⟨⟨-, -, -, -, hout, -, -, -, -, -⟩, -, -, ⟨o1, o2, o3, o4, oa, ort, ow, opa, op48, oph, opw⟩, hz1, hz2, -⟩ :=
    id hpre
  obtain ⟨hreg, hF, hLF, hLE, -, -, -⟩ := hrt
  simp only [win, K, A, outside_cons, outside_nil, and_true] at ow opw hout
  rw [natOneA_eq] at o1 o2 o3 oa ort ow hz1
  unfold Apart at hz1 hz2
  have r : ∀ a, 12050400 ≤ a → a + 8 ≤ 12050400 + 24 → M.readLE a 8 = s.mem.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    simp only [win, K, A, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨ort.of_sub h1 h2, by omega⟩, by omega⟩
  refine ⟨(r _ (by omega) (by omega)).trans o1, (r _ (by omega) (by omega)).trans o2, (r _ (by omega) (by omega)).trans o3,
    ?_, by rw [hF.accessible]; exact opa, op48, hLE.held oph, by omega, by unfold Apart; omega,
    by rw [hF.accessible]; exact oa⟩
  rw [Expmc.held_readLE oph hF hLF (by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)]
  exact o4

/-- the frame words survive stores below `e - 8` -/
theorem fw_lo' {s : State} {M M' : Memory} {zp zl zc yp n lo : Nat} (hs : 152 ≤ (s.regs 4).toNat)
    (h : Fw s M zp zl zc yp n) (hF : MemFrame M M' [(lo, (s.regs 4).toNat - 8)]) :
    Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (s.regs 4).toNat - 8 ≤ a → M'.readLE a 8 = M.readLE a 8 :=
    fun a ha => hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨(r _ ?_).trans f1, (r _ ?_).trans f2, (r _ ?_).trans f3, (r _ ?_).trans f4, (r _ ?_).trans f5,
    (r _ ?_).trans f6, (r _ ?_).trans f7⟩ <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `z = z.trunc(z, n)` returns (`+0x358`): load `natOne`, `z.add(z, natOne)`, return -/
theorem s4t (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hadd : AddHypR impl R) {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    (M0 : Memory) {L3 : List (Nat × Nat)} {b3 : Nat} (hrt0 : Rt R b L s zp zc n 3 M0 L3 b3)
    (hfw0 : Fw s M0 zp zl zc yp n) (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hv0 : natVal M0 zp (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n))
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 136)
    (h140 : S0.regs 14 = s.regs 14) (hfs0 : S0.fsBase = s.fsBase) (hx0 : S0.xmm 15 = s.xmm 15)
    (hdf0 : S0.df = false)
    (s' : State) (hpc' : s'.rip = BitVec.ofNat 64 6216696) (hsp' : s'.regs 4 = S0.regs 4 + 8)
    (h14' : s'.regs 14 = S0.regs 14) (hx' : s'.xmm 15 = S0.xmm 15) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b3 L3 stkT aboveT zp zc zp (W n) n S0 s') :
    Goal impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  have hent := ent_of hpre
  simp only [W] at hW
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hs4 : 4576 ≤ (s.regs 4).toNat := by omega
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hrt0.2.2.2.2.2.2 (by omega)).2.2.2
  obtain ⟨hfs, hdf, p', l4, c', e0, e1, e2, L4, b4, ⟨hv4, hn4, hlc4, -, hlive4, hreuse4, -⟩, -, ⟨hLE4, hb4, hinv4⟩,
    hF4, hLF4⟩ := hpost
  obtain ⟨hp, hc⟩ := hreuse4 (by unfold truncNeed; simp only [W]; omega)
  subst p' c'
  simp only [win, hsp0] at hF4
  rw [hS0] at hF4 hLF4 hreg' hv4
  rw [h140] at hinv4
  have hrt4 := rt_call hrt0 hs4 hkT (by omega) (Or.inl rfl) hreg' hF4 hLF4 hLE4 hb4 (truncNeed_le_w _ _) hinv4 hlive4
  have hfw4 := fw_call hs4 hout hzw (Or.inl rfl) hkT haT hfw0 hF4
  have hW4 : l4 ≤ W n := len_le_W hn4 (by rw [hv4]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  have hsp1 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) := by
    rw [hsp']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp0]; omega
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  have hzh4 : Held R L4 zp (8 * zc) := (hrt4.2.2.2.2.2.2 (by omega)).2.1
  obtain ⟨o1, o2, o3, -, -, -, -, -, -, ona⟩ := one_at hpre hrt4
  have hstk : s'.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt4.2.1.accessible]; exact hw
  -- every fact the `add` call needs, at any memory that differs from `s'.mem` only in the window
  have fr : ∀ M', MemFrame s'.mem M' (win s K A) → M'.regions = s'.mem.regions →
      Rt R b L s zp zc n 4 M' L4 b4 ∧ NatNorm M' zp l4 ∧ natVal M' zp l4 = natVal s'.mem zp l4 ∧
      M'.accessible zp (8 * l4) false = true ∧ NatNorm M' op 1 ∧ natVal M' op 1 = 1 ∧
      M'.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L4 op 8 ∧
      (op + 8 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ op) ∧ Apart zp (8 * zc) op 8 := by
    intro M' hF hr
    have hrt' := rt_stk hpre hrt4 hF hr
    obtain ⟨-, -, -, q4, qa, q48, qh, qw, qz, -⟩ := one_at hpre hrt'
    have hzA : Outside zp (8 * l4) (win s K A) := by
      simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
    refine ⟨hrt', natNorm_frame hF hzA hn4, natVal_frame hF hzA, ?_, Or.inr ?_, ?_, qa, q48, qh, qw, qz⟩
    · exact Janus.Arm64.Memory.accessible_sub _ (hrt'.2.2.2.2.2.2 (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _)
        (by omega)
    · rw [show op + 8 * (1 - 1) = op by omega, q4]; decide
    · unfold natVal; simpa using q4
  unfold Goal
  janus64_run [o1, o2, o3, hsp1, b136] until [6182240]
  refine addCallB hap hadd (zp := zp) (zl := l4) (zc := zc) (xp := zp) (xl := l4) (xc := zc) (yp := op) (yl := 1)
    (yc := 1) (sp' := (s.regs 4).toNat - 136) (g := (s.regs 14).toNat) (ra := 6216731)
    (bx39 := by have := hW4; simp only [W] at this; omega)
    (by39 := by omega)
    (ra_of hap (by decide) 0x37b (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
    (addPre_of hpre (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).1 (by omega) rfl ?_ ?_ ?_ hlc4
      (Nat.le_refl _) hzc (by omega) hW4 (by simp only [W]; omega) (Or.inl rfl)
      (Or.inr (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.2.2.2.2.2.2.2)
      (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.1 (by omega)
      (hzh4.sub (Nat.le_refl _) (by omega))
      (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.1 (by omega)
      (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.2.2.2.1
      (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.2.2.2.2.1
      (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.2.2.2.2.2.1
      (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.2.1
      (by have := (fr _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)).2.2.2.2.2.2.2.2.2.1; omega))
    fun s'' p5 n5 c5 L5 b5 hpc5 hsp5 h145 hx5 hfs5 hdf5 hrg5 q0 q1 q2 hv5 hn5 hlc5 hln5 hLE5 hb5 hinv5 hlive5 hor5
      hF5 hLF5 hreuse5 hc405 hp64 => ?qK
  case qK =>
    obtain ⟨Mx, hMx⟩ := memAbs hF5
    have hFx : MemFrame s'.mem Mx (win s K A) := by rw [hMx]; simp only [win, K, A]; janus_frame
    have hrx : Mx.regions = s'.mem.regions := by rw [hMx]; janus64_simp
    rw [← hMx] at hF5 hLF5 hrg5 hv5
    obtain ⟨hrtM, -, hzv, -, -, hov, -⟩ := fr Mx hFx hrx
    simp only [W] at hW4
    have hrt5 := rt_call hrtM hs4 (show 4440 ≤ 4440 by omega) (show 80 ≤ 224 by omega) (Or.inl rfl) hrg5
      hF5 hLF5 hLE5 hb5 (makeCost_le_w (by simp only [W]; split <;> omega)) hinv5 (fun hc => ?_)
    · have hfwM : Fw s Mx zp zl zc yp n :=
        fw_lo' (lo := (s.regs 4).toNat - 4576) (by omega) hfw4 (by rw [hMx]; janus_frame)
      have hfw5 := fw_call hs4 hout hzw (Or.inl rfl) (show 4440 ≤ 4440 by omega) (show 80 ≤ 80 by omega) hfwM hF5
      obtain ⟨u0, ubp, -⟩ := hfw5
      obtain ⟨x0, xbp, -⟩ := hfwM
      have hra := hent.2.1
      have c8 : (s.regs 4).toNat - 136 + 8 + 120 = (s.regs 4).toNat - 8 := by omega
      have c128 : (s.regs 4).toNat - 136 + 8 + 128 = (s.regs 4).toNat := by omega
      have c0 : (s.regs 4).toNat - 8 + 8 = (s.regs 4).toNat := by omega
      have hv' : natVal s''.mem p5 n5 = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n := by
        rw [hv5, hzv, hov, hv4, hv0, SubMod2N.lt_branch _ _ n _ (by omega) rfl hlt, SubMod2N.Bpow]
      janus64_run [hsp5, c8, c128, c0, u0, ubp, x0, xbp, hra]
      refine ⟨?_, post_of hrt5 (by omega) ?_ ?_ ?_ ?_ ?_ ?_ hn5 hlc5 hc405 hlive5 ?_
        (fun h => hreuse5 (by simp only [W] at h; split <;> omega))⟩
      all_goals first
        | (janus64_simp; done)
        | exact hent.2.2.2.2.symm
        | exact Nat.mod_eq_of_lt hp64
        | exact hv'
        | (rw [hfs5]; first | (rw [hfs, hfs0]) | (janus64_simp; rw [hfs, hfs0]))
        | (rcases hor5 with h | ⟨h1, h2⟩
           · exact Or.inl h
           · exact Or.inr ⟨h1, fresh_of hrt4.2.2.2.1 h2⟩)
        | (janus64_simp <;> first | exact hv' | exact hent.2.2.2.2.symm | exact Nat.mod_eq_of_lt hp64)
        | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    · obtain ⟨c1, c2, c3, c4⟩ := hrtM.2.2.2.2.2.2 hc
      exact ⟨c1, hLE5.held c2, by rw [hF5.accessible]; exact c3, c4⟩
  all_goals first
    | (janus64_simp; done)
    | (janus64_simp <;> first | exact hent.2.2.2.1 | (rw [hx', hx0]; exact hent.2.2.2.1) | (rw [hdf, hdf0]))
    | (janus64_simp <;> first | (rw [h14', h140]) | (rw [hfs, hfs0]) | omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s4c (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (hadd : AddHypR impl R) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) :
    J5 impl R b L op zp zl zc yp yl yc n s := by
  intro S L3 b3 hpre hpc hsp hab h0 h6 h1 h2 hfw hrt hlt hv
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  have hent := ent_of hpre
  simp only [W] at hW
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hrt.2.2.2.2.2.2 (by omega)).2.2.2
  have hzh : Held R L3 zp (8 * zc) := (hrt.2.2.2.2.2.2 (by omega)).2.1
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  have hstk : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hw
  have haccz : ∀ M', MemFrame S.mem M' (win s K A) → M'.regions = S.mem.regions →
      M'.accessible zp (8 * W n) false = true := fun M' hF hr =>
    Janus.Arm64.Memory.accessible_sub _ ((rt_stk hpre hrt hF hr).2.2.2.2.2.2 (by omega)).2.2.1 (Or.inr rfl)
      (Nat.le_refl _) (by simp only [W]; omega)
  unfold Goal
  janus64_run [b136] until [6188320]
  refine truncCall hap hns htr (zp := zp) (zl := W n) (zc := zc) (x := zp) (xl := W n) (xc := zc) (n := n)
    (ra := 6216696) (ra_of hap hnf 0x358 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega)
    (by simp only [W]; omega) (by omega)
    (truncPre_of hpre (rt_stk hpre hrt (by simp only [win, K, A]; janus_frame) (by janus64_simp)) (by omega) rfl ?_ ?_ ?_
      hkT haT (Or.inl ⟨rfl, rfl⟩) (by simp only [W]; omega) (by simp only [W]; omega)
      (haccz _ (by simp only [win, K, A]; janus_frame) (by janus64_simp)) (by simp only [W]; omega)
      (hzh.sub (Nat.le_refl _) (by simp only [W]; omega)) (by simp only [W]; omega) (by simp only [W]; omega)
      (Or.inl rfl))
    fun s' hpc' hsp' h14' hx' hreg' hpost => ?qK
  case qK =>
    refine s4t impl hap hadd hpre hkT haT _ (rt_stk hpre hrt (by simp only [win, K, A]; janus_frame) (by janus64_simp))
      (fw_lo' (lo := (s.regs 4).toNat - 4576) (by omega) hfw (by janus_frame)) hlt
      ((natVal_frame (rs := win s K A) (by simp only [win, K, A]; janus_frame)
        (by simp only [win, K, A, W, outside_cons, outside_nil, and_true]; omega)).trans hv)
      _ rfl ?_ ?_ ?_ ?_ ?_ s' hpc' hsp' h14' hx' hreg' hpost
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp <;> first | exact h14 | exact hfs | exact hdf | exact hx15 | omega)
  all_goals first
    | (janus64_simp; done)
    | (janus64_simp <;> first | exact hent.2.2.2.1 | (rw [hx15]; exact hent.2.2.2.1) | exact hdf)
    | (janus64_simp <;> first | exact h14 | exact hfs | omega)

end FvModexp.Amd64.SubMod2N
