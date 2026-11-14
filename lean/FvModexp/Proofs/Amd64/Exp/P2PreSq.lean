import FvModexp.Proofs.Amd64.Exp.P2PreRS

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `powers[i] = powers[i].sqr(stk, powers[i/2])` (nat.go:892) → `JA`
(agent divmc s65; twin of infra's `Arm64/Exp/P2PreSq`)

* `sqrCallQ`: a call of divmc's Q-form `nat.sqr` (`SqrE`, window `W`) from its entry.
* `callSqrH`: at the `nat.sqr` entry (call `+0x40e`, return `+0x413`) with `z = powers[i] = (bp + 8 i w, w, 2 w)`,
  `x = powers[i/2]` (computed), `stk`: the callee precondition from `RS` and `Pre`, and the continuation into `JA`
  (the result reuses `z`: `cap z = 2 w ≥ 2 len x` and `z`'s array end differs from `x`'s).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

theorem sqr_addr : segAddr Extracted.program Q.NatSqr.fn = 6229984 := by decide

set_option maxRecDepth 20000 in
/-- a call of the Q-form `nat.sqr` (`SqrE`, window `W`, reserve level `H`) from its entry -/
theorem sqrCallQ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    (hsq : SqrE impl R ns W) (H : Nat) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6229984) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64)
    (hpre : Q.NatSqr.SPre R b H L W zp zc st xp xl xc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Q.NatSqr.SPost R b H L W zp zc st xp xl xc S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (hsq H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc))
  rw [sqr_addr] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

theorem stkSep_sub {M : Memory} {st p n a k : Nat} (h : StkSep M st p n) (h1 : p ≤ a) (h2 : a + k ≤ p + n) :
    StkSep M st a k := by
  obtain ⟨s1, s2, s3⟩ := h
  unfold Apart at s1 s2 s3
  exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩

/-- a round's costs fit in what is left at round `i` -/
theorem bud_room {c0 r pl i b b1 : Nat} (hc : c0 + (pl / 2 - 1) * r ≤ b) (hi : i + 2 ≤ pl) (h2 : 2 ≤ i)
    (hi2 : i % 2 = 0) (hb : b - (c0 + (i / 2 - 1) * r) ≤ b1) : r ≤ b1 := by
  have : (i / 2 - 1) * r + r ≤ (pl / 2 - 1) * r := by
    have := Nat.mul_le_mul_right r (show i / 2 - 1 + 1 ≤ pl / 2 - 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  omega

/-- the invariant after a Q-form callee at the reserve level `H` -/
theorem effQ {R : RtInv} {L : List (Nat × Nat)} {g : Nat} {v : Memory} {b1 c r r' b' : Nat}
    (hinv : R.inv b' L g v) (h : b1 + r - (c + r) + r' ≤ b') :
    ∃ b2, R.inv (b2 + r') L g v ∧ b1 - c ≤ b2 :=
  ⟨b' - r', by rw [Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callSqrH (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s) {i : Nat}
    (kA : JA impl R kc b L st pw pl ws lm x xl s i) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrs : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M L1 b1 i i)
    (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl) (hb : b - (tC lm + (i / 2 - 1) * rc lm) ≤ b1)
    (S' : State) (hpc : S'.rip = BitVec.ofNat 64 6229984) (hfr : Frm s S' 184)
    (hm : S'.mem = M.writeLE ((s.regs 4).toNat - 176 - 8) 8 6196499)
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * (i * W lm))) (h3 : S'.regs 3 = BitVec.ofNat 64 (W lm))
    (h1 : S'.regs 1 = BitVec.ofNat 64 (2 * W lm)) (h7 : S'.regs 7 = BitVec.ofNat 64 st)
    (h6 : S'.regs 6 = BitVec.ofNat 64 (bp + 8 * (i / 2 * W lm)))
    {xl' : Nat} (hxl : M.readLE (pw + 24 * (i / 2) + 8) 8 = xl') (h8 : S'.regs 8 = BitVec.ofNat 64 xl')
    (h9 : S'.regs 9 = BitVec.ofNat 64 (W lm)) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S' (GoalQ R kc b L st pw pl lm x xl s) := by
  have h64 : (64 : Nat) ≤ 88 := by decide
  have hf := pf_of hpre (by omega)
  have hR64 := (s.regs 4).isLt
  have hK := hf.w.sp
  simp only [K] at hK
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr
  have hspN : (S'.regs 4).toNat = (s.regs 4).toNat - 184 := by rw [hsp]; exact tN (by omega)
  have hadd8 : BitVec.ofNat 64 ((s.regs 4).toNat - 184) + 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨-, hsv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlen0, -, hcost, -, hwt, hadx, -, hx15s,
    hdfs⟩ := id hpre
  have hrs' := rs_own hpre hkc hrs (by omega) 6196499 (a0 := (s.regs 4).toNat - 176 - 8) (by omega) (by omega)
  rw [← hm] at hrs'
  have hc := hrs'.c
  have hxl' : S'.mem.readLE (pw + 24 * (i / 2) + 8) 8 = xl' := by
    have hpw := hf.pww
    simp only [K, A, win, outside_cons, outside_nil, and_true] at hpw
    rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hxl
  obtain ⟨-, -, d1, dv, -⟩ := hrs'.d (i / 2) (by omega)
  rw [hxl'] at d1 dv
  have hb48 := hc.scr.b48
  have hal := hc.scr.al
  have hnb := nb_le hpl16 hw128
  have hsep := pw_sep (lm := lm) (j := i / 2) (k := i) (by omega)
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i) (by omega)
  have hroom := bud_room hcost hip hi hi2 hb
  have hsqm : sqrCQ xl' ≤ sqrCQ (W lm) := sqrCQ_mono d1
  have hz := bufArr hpre hc hf hspN h14 hfs rfl hkS h64 (a := bp + 8 * (i * W lm)) (c := 2 * W lm)
    (by omega) hin (by omega) (by omega) (by omega)
  have hx := bufArr hpre hc hf hspN h14 hfs rfl hkS h64 (a := bp + 8 * (i / 2 * W lm)) (c := W lm)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hst : stLen S'.mem st = stLen s.mem st + StackNat.rnd (NB pl lm) := hc.sa.2.1
  have hxd := hx.2 xl' d1
  have hxW := hx.2 (W lm) (Nat.le_refl _)
  have hzo := hz.1.2.2 (by omega)
  have hsapz := stkSep_sub (a := bp + 8 * (i * W lm)) (k := 8 * (2 * W lm)) hc.sap (by omega) (by omega)
  have hsapx := stkSep_sub (a := bp + 8 * (i / 2 * W lm)) (k := 8 * xl') hc.sap (by omega) (by omega)
  have hra : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5e8900 + 0x413 := by
    rw [hspN, hm, (show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 176 - 8 by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
  refine sqrCallQ hap hns hsq (HP (stLen s.mem st) pl lm) (b := b1 + stkR (HP (stLen s.mem st) pl lm) S'.mem st)
    (L := L1) (ra_bp hap hnf 0x413 (by decide)) hpc hra
    h0 h3 h1 h7 h6 h8 h9 (by rw [hx15, hx15s]) (by rw [hdf, hdfs]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
    ⟨callEnv_ctx hpre hc hspN h14 hfs rfl hkS h64, by unfold sqrW ksqrW at hkS1 ⊢; omega, hsv,
      globals_ctx hpre hc hspN hkS h64, hwt, d1, by omega, by omega, hxd.2.1,
      fun _ => ⟨hxW.2.2.2.1, hxW.2.2.1⟩, fun _ => hxd.2.2.2.2, by omega, hz.1.2.1, hzo.1,
      fun _ => ⟨hzo.2.1, hzo.2.2, hsapz⟩, Or.inr fun _ _ => by unfold Apart; omega,
      stkPre_ctx hpre hc hspN h14 hfs rfl hkS h64, fun _ => hsapx,
      by rw [hst]; simp only [StackNat.rnd]; omega,
      ⟨by rw [hst]; simp only [HP, DPre]; omega, by simp only [rc] at hroom; omega⟩,
      by rw [hc.fr.accessible]; exact hadx, by rw [h14]; exact hc.inv⟩
    fun s' hpc' hsp' h5' h14' hx15' hrg hpost => ?_
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, hv', hn', hlc', hl2, hc40', L', b', hLE, hbud', hinv', -, -, -, hreu,
    hsbl, hF', hLF'⟩ := hpost
  obtain ⟨rfl, rfl, -⟩ := hreu (by omega) (by omega)
  rw [h14] at hinv'
  obtain ⟨b2, hinv2, hbud2⟩ := effQ hinv' hbud'
  have hws : ∀ r ∈ [(bp + 8 * (i * W lm), bp + 8 * (i * W lm) + 8 * (2 * W lm))] ++ stkWs S'.mem st,
      WOK R L s st r := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact wok_buf hc.scr (by omega) hin
    · exact wok_stk hc.sa r hr
  have hF2 : MemFrame S'.mem s'.mem (R.rt ++ win S' kS 64 ++ ([(bp + 8 * (i * W lm),
      bp + 8 * (i * W lm) + 8 * (2 * W lm))] ++ stkWs S'.mem st)) := by rw [List.append_assoc] at hF'; exact hF'
  have hc2 := keepC hc hf.w hspN hkS h64 hws hF2 hLF' hrg hLE hinv2 (sa_back hc.sa hsbl.1 hc.le)
    (sap_back hc.sap hc.scr.held hsbl.1) (hc.ain.trans hsbl.2 hLE) (bu_back hc.bu hc.scr.held hsbl.1)
  have hrs2 := rs_call hrs' hf (pw_sep_stk hpre) hspN hkS h64 (fun r hr => hr) hws (Nat.le_refl _)
    (by omega) hF2 hLF' hc2
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by rw [hsp', hsp]; exact hadd8
  refine kA s' bp L' b2 l' hpre hpc' ⟨hsp2, h5'.trans h5, h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15,
    hdf'.trans hdf⟩ e0 e3 e1 hrs2 (by omega) (hv'.trans (by rw [dv])) hn' hi2 hi hip ?_
  simp only [rc] at hroom hb ⊢
  omega

end

end FvModexp.Amd64.P2Pre
