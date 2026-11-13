import FvModexp.Proofs.Amd64.Exp.SubMod2NGC

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: after `z = z.trunc(z, n)` returns (`+0x358`): load `natOne`,
`return z.add(z, natOne)` (nat.go:1754-1755) on the current array `(p, c)` (agent infra s49; twin of
Arm64/Exp/SubMod2NGS4C.lean, amd64 code as the `Pre` chain's Amd64/Exp/SubMod2NS4C.lean)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

theorem natOneG_eq : natOneA = 12050400 := by decide

/-- name the memory of a symbolic state -/
theorem memAbsG {M M2 : Memory} {rs : List (Nat × Nat)} (_h : MemFrame M M2 rs) : ∃ Mx, Mx = M := ⟨M, rfl⟩

/-- the frame words survive stores below `e - 8` (copy of `fwG_lo`, SubMod2NGS3.lean, kept off that chain) -/
theorem fwG_loC {s : State} {M M' : Memory} {zp zl zc yp n lo : Nat} (hs : 152 ≤ (s.regs 4).toNat)
    (h : Fw s M zp zl zc yp n) (hF : MemFrame M M' [(lo, (s.regs 4).toNat - 8)]) :
    Fw s M' zp zl zc yp n := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  have r : ∀ a, (s.regs 4).toNat - 8 ≤ a → M'.readLE a 8 = M.readLE a 8 :=
    fun a ha => hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨(r _ ?_).trans f1, (r _ ?_).trans f2, (r _ ?_).trans f3, (r _ ?_).trans f4, (r _ ?_).trans f5,
    (r _ ?_).trans f6, (r _ ?_).trans f7⟩ <;> omega

/-- the budget base after `g` growths still covers the remaining calls -/
theorem bb_ok {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {g : Nat} (hg : g ≤ W n) (hgz : W n ≤ zc → g = 0) :
    cost n ≤ b - g * gA n := by
  have hc := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases h : W n ≤ zc
  · rw [hgz h, Nat.zero_mul, Nat.sub_zero]; exact hc.1
  · have h1 := hc.2 (by omega)
    have h2 : g * gA n ≤ W n * gA n := Nat.mul_le_mul_right _ hg
    simp only [costG] at h1; omega

set_option maxRecDepth 20000 in
/-- the global `natOne` survives the function's writes (any budget base `bb`) -/
theorem oneG_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R bb L s zp zc n k M L1 b1) :
    M.readLE 12050400 8 = op ∧ M.readLE 12050408 8 = 1 ∧ M.readLE 12050416 8 = 1 ∧ M.readLE op 8 = 1 ∧
      M.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L1 op 8 ∧
      (op + 8 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ op) ∧
      M.accessible 12050400 24 false = true := by
  obtain ⟨⟨-, -, -, -, hout, -, -, -, -, -⟩, -, -, ⟨o1, o2, o3, o4, oa, ort, ow, opa, op48, oph, opw⟩, hz1, hz2, -⟩ :=
    id hpre
  obtain ⟨hreg, hF, hLF, hLE, -, -, -⟩ := hrt
  simp only [win, K, A, outside_cons, outside_nil, and_true] at ow opw hout
  rw [natOneG_eq] at o1 o2 o3 oa ort ow hz1
  unfold Apart at hz1 hz2
  have r : ∀ a, 12050400 ≤ a → a + 8 ≤ 12050400 + 24 → M.readLE a 8 = s.mem.readLE a 8 := by
    intro a h1 h2
    refine hF.readLE _ _ ?_
    simp only [win, K, A, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨ort.of_sub h1 h2, by omega⟩, by omega⟩
  refine ⟨(r _ (by omega) (by omega)).trans o1, (r _ (by omega) (by omega)).trans o2, (r _ (by omega) (by omega)).trans o3,
    ?_, by rw [hF.accessible]; exact opa, op48, hLE.held oph, by omega, by rw [hF.accessible]; exact oa⟩
  rw [Expmc.held_readLE oph hF hLF (by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)]
  exact o4

/-- the written range `(p, p + 8c)` of a call on the current array, in `rt_callG`'s form -/
theorem zr_cur {R : RtInv} {L : List (Nat × Nat)} {zp zc p c : Nat} (h : CurA R L zp zc p c) :
    (p, p + 8 * c) = (zp, zp + 8 * zc) ∨ (p + 8 * c) = 0 ∨
      (p ≤ p + 8 * c ∧ InRanges p (p + 8 * c - p) R.rt ∧ ApartAll p (p + 8 * c - p) L) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨by omega, by rwa [show p + 8 * c - p = 8 * c by omega], by
      rwa [show p + 8 * c - p = 8 * c by omega]⟩)

/-- the facts of the `add` call at a memory that differs from `M` only in the function's window -/
@[reducible] def AddF (R : RtInv) (bb : Nat) (L : List (Nat × Nat)) (s : State) (zp zc n : Nat) (L4 : List (Nat × Nat))
    (b4 op p c l4 : Nat) (M M' : Memory) : Prop :=
  Rt R bb L s zp zc n 4 M' L4 b4 ∧ NatLive M' R L4 p c ∧ NatNorm M' p l4 ∧ natVal M' p l4 = natVal M p l4 ∧
    M'.accessible p (8 * l4) false = true ∧ NatNorm M' op 1 ∧ natVal M' op 1 = 1 ∧
    M'.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L4 op 8 ∧
    (op + 8 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ op)

set_option maxRecDepth 20000 in
theorem addF_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} {M M' : Memory} {L4 : List (Nat × Nat)} {b4 p c l4 : Nat}
    (hrt : Rt R bb L s zp zc n 4 M L4 b4) (hlv : NatLive M R L4 p c) (hn : NatNorm M p l4) (hlc : l4 ≤ c) (hc0 : 0 < c)
    (hpw : p + 8 * c ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ p)
    (hF : MemFrame M M' (win s K A)) (hr : M'.regions = M.regions) :
    AddF R bb L s zp zc n L4 b4 op p c l4 M M' := by
  have hrt' := rtG_stk hpre hrt hF hr
  obtain ⟨-, -, -, q4, qa, q48, qh, qw, -⟩ := oneG_at hpre hrt'
  have hzA : Outside p (8 * l4) (win s K A) := by
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  have hlv' : NatLive M' R L4 p c := fun hc => by
    obtain ⟨c1, c2, c3, c4⟩ := hlv hc
    exact ⟨c1, c2, by rw [hF.accessible]; exact c3, c4⟩
  refine ⟨hrt', hlv', natNorm_frame hF hzA hn, natVal_frame hF hzA, ?_, Or.inr ?_, ?_, qa, q48, qh, qw⟩
  · exact Janus.Arm64.Memory.accessible_sub _ (hlv' hc0).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  · rw [show op + 8 * (1 - 1) = op by omega, q4]; decide
  · unfold natVal; simpa using q4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `z = z.trunc(z, n)` returns (`+0x358`): load `natOne`, `z.add(z, natOne)`, return -/
theorem s4tG (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hadd : AddHypR impl R) {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    {p c g : Nat} (hcur : CurA R L zp zc p c) (hc40 : c < 2 ^ 40) (hp64 : p < 2 ^ 64) (hWc : W n ≤ c)
    (hg : g ≤ W n) (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0)
    (M0 : Memory) {L3 : List (Nat × Nat)} {b3 : Nat} (hrt0 : Rt R (b - g * gA n) L s zp zc n 3 M0 L3 b3)
    (hlv0 : NatLive M0 R L3 p c)
    (hfw0 : Fw s M0 zp zl zc yp n) (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (hv0 : natVal M0 p (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n))
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 136)
    (h140 : S0.regs 14 = s.regs 14) (hfs0 : S0.fsBase = s.fsBase) (hx0 : S0.xmm 15 = s.xmm 15)
    (hdf0 : S0.df = false)
    (s' : State) (hpc' : s'.rip = BitVec.ofNat 64 6216696) (hsp' : s'.regs 4 = S0.regs 4 + 8)
    (h14' : s'.regs 14 = S0.regs 14) (hx' : s'.xmm 15 = S0.xmm 15) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b3 L3 stkT aboveT p c p (W n) n S0 s') :
    GoalG impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -⟩ := id hpre
  have hent := hpre.ent
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hout hb' ha hw
  have hs4 : 4576 ≤ (s.regs 4).toNat := by omega
  have hbb := bb_ok hpre hg fun h => (hgz h).2.2
  obtain ⟨hpw, hpg, hpf, -, hpo⟩ := curA_win hpre hcur
  have hW1 : 1 ≤ W n := by have := hpre.2.2.2.2.2.2.1; simp only [W]; omega
  obtain ⟨hfs, hdf, p', l4, c', e0, e1, e2, L4, b4, ⟨hv4, hn4, hlc4, -, hlive4, hreuse4, -⟩, -, ⟨hLE4, hb4, hinv4⟩,
    hF4, hLF4⟩ := hpost
  obtain ⟨hp, hc⟩ := hreuse4 (by unfold truncNeed; simp only [W] at hWc ⊢; omega)
  subst p' c'
  simp only [win, hsp0] at hF4
  rw [hS0] at hF4 hLF4 hreg' hv4
  rw [h140] at hinv4
  have hrt4 := rt_callG hrt0 hs4 hkT (by omega) (zr_cur hcur) hreg' hF4 hLF4 hLE4 hb4 (truncNeed_le_w _ _) hinv4
    (fun hc => by
      obtain ⟨c1, c2, c3, c4⟩ := hrt0.2.2.2.2.2.2 hc
      exact ⟨c1, hLE4.held c2, by rw [hF4.accessible]; exact c3, c4⟩)
  have hfw4 := fw_callG hs4 hout (Or.inr (by simp only; omega)) hkT haT hfw0 hF4
  have hW4 : l4 ≤ W n := len_le_W hn4 (by rw [hv4]; exact Nat.mod_lt _ (Nat.two_pow_pos n))
  have hsp1 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) := by
    rw [hsp']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp0]; omega
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  have hzh4 : Held R L4 p (8 * c) := (hlive4 (by omega)).2.1
  obtain ⟨o1, o2, o3, -, -, -, -, -, ona⟩ := oneG_at hpre hrt4
  have hstk : s'.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt4.2.1.accessible]; exact hw
  unfold GoalG
  have hp48 : p + 8 * c ≤ 2 ^ 48 := (hlive4 (by omega)).2.2.2
  janus64_run [o1, o2, o3, hsp1, b136] until [6182240]
  have hF1 : MemFrame s'.mem (Janus.Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 136) 8 6216731) (win s K A) := by
    simp only [win, K, A]; janus_frame
  have hr1 : (Janus.Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 136) 8 6216731).regions = s'.mem.regions := by
    janus64_simp
  obtain ⟨hrtM, hlvM, hnM, hzvM, hzaM, honM, hovM, hoaM, ho48, hohM, howM⟩ :=
    addF_of (op := op) hpre hrt4 hlive4 hn4 hlc4 (by omega) hpw hF1 hr1
  have hfwM := fwG_loC (lo := (s.regs 4).toNat - 4576)
    (M' := Janus.Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 136) 8 6216731) (by omega) hfw4 (by janus_frame)
  refine addCallW hap hadd (zp := p) (zl := l4) (zc := c) (xp := p) (xl := l4) (xc := c) (yp := op) (yl := 1)
    (yc := 1) (sp' := (s.regs 4).toNat - 136) (g := (s.regs 14).toNat) (ra := 6216731)
    (M := Janus.Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 136) 8 6216731)
    (bx39 := by simp only [W] at hW4; omega) (by39 := by omega)
    (ra_of hap (by decide) 0x37b (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
    (addPreG_of hpre hbb hrtM (Nat.le_refl _) rfl ?_ ?_ ?_ (by omega) hc40 hlvM hp64 (fun _ => ⟨hpw, hpg, hpf⟩) hlc4
      (Nat.le_refl _) hc40 (by omega) hW4 hW1 (Or.inl rfl) (Or.inr hpo) hzaM (by omega)
      (hzh4.sub (Nat.le_refl _) (by omega)) hnM (by omega) hoaM ho48 hohM honM (by omega))
    fun s'' p5 n5 c5 L5 b5 hpc5 hsp5 h145 hx5 hfs5 hdf5 hrg5 q0 q1 q2 hv5 hn5 hlc5 hln5 hLE5 hb5 hinv5 hlive5 hor5
      hF5 hLF5 hreuse5 hc405 hp5 => ?qK
  case qK =>
    simp only [W] at hW4
    have hrt5 := rt_callG hrtM hs4 (show 4440 ≤ 4440 by omega) (show 80 ≤ 224 by omega) (zr_cur hcur) hrg5
      hF5 hLF5 hLE5 hb5 (makeCost_le_w (by simp only [W]; split <;> omega)) hinv5 (fun hc => ?_)
    · have hfw5 := fw_callG hs4 hout (Or.inr (by simp only; omega)) (show 4440 ≤ 4440 by omega)
        (show 80 ≤ 80 by omega) hfwM hF5
      obtain ⟨u0, ubp, -⟩ := hfw5
      obtain ⟨x0, xbp, -⟩ := hfwM
      have hra := hent.2.1
      have c8 : (s.regs 4).toNat - 136 + 8 + 120 = (s.regs 4).toNat - 8 := by omega
      have c128 : (s.regs 4).toNat - 136 + 8 + 128 = (s.regs 4).toNat := by omega
      have c0 : (s.regs 4).toNat - 8 + 8 = (s.regs 4).toNat := by omega
      have hv' : natVal s''.mem p5 n5 = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n := by
        rw [hv5, hzvM, hovM, hv4, hv0, SubMod2N.lt_branch _ _ n _ (by omega) rfl hlt, SubMod2N.Bpow]
      janus64_run [hsp5, c8, c128, c0, u0, ubp, x0, xbp, hra]
      refine ⟨?_, post_ofG hrt5 (by omega) hg (fun h => (hgz h).2.2) ?_ ?_ ?_ ?_ ?_ ?_ hn5 hlc5 hc405 hlive5 ?_
        (fun h => ?_)⟩
      all_goals try janus64_simp
      · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · rw [hfs5]; exact hfs.trans hfs0
      · exact hent.2.2.2.2.symm
      · exact hv'
      · rcases hor5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases hcur with ⟨f1, f2⟩ | ⟨h3, h4⟩
          · exact Or.inl ⟨h1.trans f1, h2.trans f2⟩
          · exact Or.inr ⟨h1 ▸ h2 ▸ h3, h1 ▸ h2 ▸ h4⟩
        · exact Or.inr ⟨h1, fresh_of hrt4.2.2.2.1 h2⟩
      · have hW' : W n ≤ zc := Nat.le_of_succ_le h
        obtain ⟨f1, f2, -⟩ := hgz hW'
        have hn' : (if min l4 1 = 0 then max l4 1 else max l4 1 + 1) ≤ c := by
          rw [f2]; simp only [W] at h; split <;> omega
        exact ⟨(hreuse5 hn').1.trans f1, (hreuse5 hn').2.trans f2⟩
    · obtain ⟨c1, c2, c3, c4⟩ := hrtM.2.2.2.2.2.2 hc
      exact ⟨c1, hLE5.held c2, by rw [hF5.accessible]; exact c3, c4⟩
  all_goals try janus64_simp
  · exact hent.2.2.2.1
  · omega
  · omega
  · rw [hfs, hfs0]

end FvModexp.Amd64.SubMod2N
