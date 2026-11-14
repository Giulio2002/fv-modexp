import FvModexp.Proofs.Amd64.Exp.EvTrD
import FvModexp.Proofs.Amd64.Exp.EvTrR
import FvModexp.Proofs.Amd64.Exp.EvSm
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): **`segTr`** — `J12` (`mul1R`) → `z2 = z2.trunc(z2, n)` → `J13` (`trR`) (asm s63; twin of
infra's arm64 `EvTr`)

`runTr` pushes `trR`; premise `TrHyp0` (= asm's amd64 `Trunc.Hyp0`, window `4192 / 64`); `z = x = t`, so `trunc`
reuses `t`'s array (`need = min(len t, ⌈n/64⌉) ≤ cap t`); a non-stack callee (`frm_dst`, possibly EMPTY `t`);
`m2`, `z`, `z3` survive. Slot reads through `kk_push1` / `t_slot` (PERF LESSON s62).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp

theorem tNT {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem vT_lt (s : State) (xp xl yp yl mp ml : Nat) :
    vT s xp xl yp yl mp ml < 2 ^ (nE s mp ml + nE s mp ml) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' (Exp.subMod2N_spec _ _ _).1 (mi_lt _ _)

/-- the keep range through the push and a callee with `above ≤ 0x7f` -/
theorem kk_push1 {sp : Nat} {M0 M M' : Memory} {ab : Nat} (hsp : 8 ≤ sp) (hab : ab ≤ 0x7f)
    (hF : MemFrame M0 M [(sp - 8, sp)])
    (hkc : ∀ a k, sp - 8 + ab ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) :
    ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k := fun a k h1 h2 => by
  rw [hkc a k (by omega) h2, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]

theorem t_slot {sp : Nat} {M0 M' : Memory}
    (hk : ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k) (o : Nat) (h1 : 0x77 ≤ o)
    (h2 : o + 8 ≤ 0x1b8) {v : Nat} (h : M0.readLE (sp + o) 8 = v) : M'.readLE (sp + o) 8 = v := by
  rw [hk _ _ (by omega) (by omega)]; exact h

theorem own1 (sp K : Nat) (hsp : 8 ≤ sp) : ∀ r ∈ [(sp - 8, sp)], OwnR sp K r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only [OwnR]; omega

theorem need_le {lt n ct : Nat} (h : lt ≤ ct) : truncNeed lt n ≤ ct := Nat.le_trans (Nat.min_le_left _ _) h

theorem lt2 {lt ml n : Nat} (hn : n < 64 * ml) (hml : ml ≤ 128) (h : lt ≤ 2 * ml) : lt ≤ 2 ^ 16 ∧ n ≤ 2 ^ 20 := by
  omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a live local as an empty-tolerant callee input at `RSP = sp - 8` -/
theorem LN.rd0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {p l c v : Nat} (h : LN R L s.mem st M L1 p l c v) {S : State}
    (hsp : (S.regs 4).toNat = sp - 8) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x7f) :
    RdIn0 R L1 S stk above p l :=
  ⟨Nat.lt_of_le_of_lt h.2.1 h.1.1, fun h0 => LN.rd hP h (Nat.lt_of_lt_of_le h0 h.2.1) hsp hm hstk habove⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J12` → `J13`** (see the module doc) -/
theorem segTr {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    (htr : TrHyp0 impl R ns 4192 64)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0)
    {rk rk' : Nat} (hrk : ∀ k, k ≤ 2 * ml → makeCost k + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K13 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lu ct : Nat),
      J13 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lu ct →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct : Nat}
    (h : J12 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 l1 q l2 lw pZ cZ p3 l3 c3 pt lt ct) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
  have hspl : sp < 2 ^ 64 := by omega
  have hK8 : 4192 ≤ sp - 8 := by omega
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hb0 : S.mem.readLE (sp + 0xb0) 8 = nE s mp ml := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlt2 : lt ≤ 2 * ml := nlen_bd' h.t.2.2.2 (by
    rw [h.t.2.2.1]
    exact Nat.lt_of_lt_of_le (vT_lt _ _ _ _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hct := h.t.1.1
  have hltc := h.t.2.1
  have hneed := need_le (n := nE s mp ml) hltc
  obtain ⟨hlt16, hn20⟩ := lt2 hnl hml hlt2
  have hrk' := hrk _ (Nat.le_trans (Nat.min_le_left _ _) hlt2 : truncNeed lt (nE s mp ml) ≤ 2 * ml)
  have hn64 : nE s mp ml < 2 ^ 64 := by omega
  refine runTr ret0 Q sp (nE s mp ml) S.mem hacc0 hsp8 (by omega) hb0 S h.pc h.jx.esp rfl ?_
  intro S2 M2 f0 f4 fm hF hrg frd r0 r3 r1 r7 r6 r8 r9 r5 r14 rfs rx15 rdf
  obtain ⟨hw2, hown⟩ := WC.own hP hw hF hrg (own1 sp K hsp8)
  have hhd : HdrEq st S.mem M2 := by
    have kF : ∀ a, (a + 8 ≤ sp - 8 ∨ sp ≤ a) → M2.readLE a 8 = S.mem.readLE a 8 := fun a h1 =>
      hF.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hstw := hP.stkF.1
    unfold Apart at hstw
    refine ⟨?_, kF _ (by omega), kF _ (by omega)⟩
    have := kF (st + 0) (by omega); simpa using this
  have hm2 := hown _ _ _ _ h.m2
  have hz3 := hown _ _ _ _ h.z3
  have ht0 := hown _ _ _ _ h.t
  have hzs := LZ.frm hP hw (LiveExt.refl R L1) hF.accessible hhd (d := 0) (n := 0)
    (fun a k _ hw0 _ => hF.readLE a k (by
      unfold Apart at hw0; simp only [outside_cons, outside_nil, and_true]; omega)) h.zs
    (fun _ => by unfold Apart; omega)
  have tsp : (S2.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S2.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S2.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  have hce := CallW.callEnv_of (hw2.cenv hP) tsp tg tfs fm (stk := 4192) (above := 64) (by omega) (by decide) hK8
  have hwr := DL.wr hP ht0.1 tsp tg tfs fm (stk := 4192) (above := 64) (by omega) (by decide)
  have hrd := LN.rd0 hP ht0 tsp fm (stk := 4192) (above := 64) (by omega) (by decide)
  have hS := Ensures.toSummaryIn (htr b1 L1 (BitVec.ofNat 64 pt) (BitVec.ofNat 64 lt) (BitVec.ofNat 64 ct)
    (BitVec.ofNat 64 pt) (BitVec.ofNat 64 lt) (BitVec.ofNat 64 ct) (BitVec.ofNat 64 (nE s mp ml)))
    (A64.noExit_restrict64 hap ns) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap hns)
  rw [trunc_aE] at hS
  have t1 := tNT h.pt64
  have t2 := tNT (show lt < 2 ^ 64 by omega)
  have t3 := tNT (show ct < 2 ^ 64 by omega)
  have t4 := tNT hn64
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, ?pre⟩
    (fun s' hr hq hrg' => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap hnf 1222 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0.trans h.r0, r3.trans h.r3, r1.trans h.r1, r7.trans h.r0, r6.trans h.r3, r8.trans h.r1, r9, trivial⟩
  case pre =>
    rw [t1, t2, t3, t4]
    exact ⟨⟨hce, hP.1.2.2.2.2.2.2.2.2.2, hltc, hwr, hrd, hlt16, hn20, Or.inl rfl, bud_pre hb1 hrk',
      by rw [tg, fm]; exact hw2.inv⟩, Or.inl (by rw [fm]; exact ht0.2.2.2), Or.inl rfl, fun _ => rfl⟩
  obtain ⟨⟨e4, -, e14, ex15⟩, hq⟩ := hq
  simp only [t1, t3, t2, t4] at hq
  obtain ⟨efs, edf, p', l', c', g0, g3, g1, L2, b2, ⟨hv, hN, hlc, hc40, hlv, hke, -⟩, -, ⟨hx, hb, hinv⟩, hF', hLF'⟩ :=
    hq
  obtain ⟨rfl, rfl⟩ := hke hneed
  simp only [win, tsp] at hF'
  rw [fm] at hF' hLF' hrg' hv
  rw [ht0.2.2.1] at hv
  rw [tg] at hinv
  obtain ⟨qd, kd, hds, hdl, hdw, hF'', hLF'', hsb, ehd, hapd⟩ :=
    frm_dst hP hw2 ht0 hx (stk := 4192) (above := 64) (by omega) (by decide) hF' hLF'
  obtain ⟨hw', hkc, hkeep⟩ := stepC hP hw2 hds hdl hdw (stk := 4192) (above := 64) (by omega) (by decide) hF'' hLF''
    hrg' hx hinv hsb
  have hk' := kk_push1 hsp8 (by decide) hF hkc
  have hm2' := hkeep _ _ _ _ hm2 fun c0 => hapd _ _ c0 fun ct0 => (h.tq ct0).symm
  have hz3' := hkeep _ _ _ _ hz3 fun c0 => hapd _ _ c0 fun ct0 => (h.t3 ct0 c0).symm
  have hzs' := LZ.step hP hw2 (stk := 4192) (above := 64) (by omega) (by decide) hF'' hLF'' hx hsb hzs
    fun c0 => hapd _ _ c0 fun ct0 => (h.tz ct0 c0).symm
  have ht := LN.of_sm hP hw2 ht0 hv hN hlc hc40 hlv (Or.inl ⟨rfl, rfl⟩) hx hsb (fun _ hne => absurd ehd hne)
  have hS4 : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, f4]; exact bv_add8 hsp8 hspl
  have hjx := h.jx.call (hS4.trans h.jx.esp.symm) (e14.trans r14) (by rw [efs, rfs]) (ex15.trans rx15)
    (edf.trans rdf) hw' hk' (bud_step hb1 hrk' hb)
  exact K13 s' L2 b2 l1 q l2 lw pZ cZ p3 l3 c3 p' l' c' ⟨hjx, by rw [hr, retAddrOf_eq, tsp, fm, frd], h.l1m,
    g0, g3, g1,
    t_slot hk' 0x110 (by decide) (by decide) h.s110, t_slot hk' 0xb8 (by decide) (by decide) h.sb8,
    t_slot hk' 0xc0 (by decide) (by decide) h.sc0, t_slot hk' 0x108 (by decide) (by decide) h.s108,
    t_slot hk' 0xa0 (by decide) (by decide) h.sa0, t_slot hk' 0xa8 (by decide) (by decide) h.sa8,
    t_slot hk' 0x100 (by decide) (by decide) h.s100, t_slot hk' 0x90 (by decide) (by decide) h.s90,
    t_slot hk' 0x98 (by decide) (by decide) h.s98,
    hm2', hzs', h.pZ64, h.Ze, h.Za2, hz3', h.p364, h.z3e, h.ta2, h.tZ, ht, h.pt64, h.te, h.tq, h.tz, h.t3⟩

end

end FvModexp.Amd64.ExpEven
