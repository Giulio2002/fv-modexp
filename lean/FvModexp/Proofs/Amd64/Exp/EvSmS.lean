import FvModexp.Proofs.Amd64.Exp.EvSm
import FvModexp.Proofs.Amd64.Exp.EvCall

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): **`segSm`** — `J9` (`mvJ`) → `z1 = z1.subMod2N(z1, z2, n)` → `J10` (`smR`) (asm s62;
twin of infra's arm64 `EvSmS`)

Premise `SubMod2N.EnsG impl R` (infra's general amd64 summary on `LibW`: any `cap z1`, empty `z1` / `z2`); `PreG`
from `smPre` after `runSm`'s writes (push + `n` at `[sp]`, `WC.own`); a non-stack callee (`frm_dst`, `stepC`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`J9` → `J10`** (see the module doc) -/
theorem segSm {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hE : SubMod2N.EnsG impl R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : SubMod2N.costG (nE s mp ml) + rk' ≤ rk)
    {ret0 : W64} {Q : State → Prop}
    (K10 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 : Nat),
      J10 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk' S L1 b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : J9 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hk := hP.kf
  have hce0 := hP.cenv0
  have hstw := hP.stkF.1
  unfold Apart at hstw
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hsp8 : 8 ≤ sp := by omega
  have hw := h.jx.wc
  have hacc0 : S.mem.accessible (sp - 8) 0x1c0 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hce0.2.2.2.1 (by omega) (by omega)
  have hb0 : S.mem.readLE (sp + 0xb0) 8 = nE s mp ml := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- the limb bounds (values below `2^(64 ml)`)
  have hMl : natVal s.mem mp ml < 2 ^ (64 * ml) := natVal_lt64 _ _ _
  have hodd : natVal s.mem mp ml / 2 ^ nE s mp ml % 2 = 1 := (Exp.tz_spec hM).2
  have hq0 : 0 < natVal s.mem mp ml / 2 ^ nE s mp ml := by
    rcases Nat.eq_zero_or_pos (natVal s.mem mp ml / 2 ^ nE s mp ml) with e | e
    · rw [e] at hodd; exact absurd hodd (by decide)
    · exact e
  have hl1 : lz ≤ 2 ^ 12 := len_bdE h.z1.2.2.2 h.z1.2.2.1 (Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_lt_pow_right (by decide) hnl)) hml
  have hl2 : lw ≤ 2 ^ 12 := len_bdE h.z2.2.2.2 h.z2.2.2.1 (Nat.lt_of_lt_of_le (Nat.mod_lt _ hq0)
    (Nat.le_trans (Nat.div_le_self _ _) (Nat.le_of_lt hMl))) hml
  refine runSm ret0 Q sp pz lz cz (nE s mp ml) pw lw cw S.mem hacc0 hsp8 (by omega) h.s100 h.s90 h.s98 hb0 S h.pc
    h.jx.esp rfl h.r0 h.r1 h.r6 ?_
  intro S' M' f0 f4 fm hFp hrgp frd fnr r0 r3 r1 r7 r6 r8 r9 r10 r11 r5 r14 rfs rx15 rdf
  -- the writes `[sp - 8, sp + 8)`
  obtain ⟨hwp, hlnp⟩ := WC.own hP hw hFp hrgp (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [OwnR]; omega)
  have kF : ∀ a k, Apart a k (sp - 8 - K) (K + 0x1c0) → M'.readLE a k = S.mem.readLE a k := fun a k ha =>
    hFp.readLE a k (by unfold Apart at ha; simp only [outside_cons, outside_nil, and_true]; omega)
  have hhd : HdrEq st S.mem M' := by
    refine ⟨?_, kF _ _ (by unfold Apart; omega), kF _ _ (by unfold Apart; omega)⟩
    have := kF (st + 0) 8 (by unfold Apart; omega); simpa using this
  have hzsp := LZ.frm hP hw (LiveExt.refl R L1) hFp.accessible hhd (d := 0) (n := 0)
    (fun a k _ ha _ => kF a k ha) h.zs (fun _ => by unfold Apart; omega)
  have hz1 := hlnp _ _ _ _ h.z1
  have hz2 := hlnp _ _ _ _ h.z2
  have tsp : (S'.regs 4).toNat = sp - 8 := by rw [f4, BitVec.toNat_ofNat]; omega
  have tg : (S'.regs 14).toNat = g := by rw [r14, h.jx.e14, BitVec.toNat_ofNat]; omega
  have tfs : S'.fsBase.toNat = fs := by rw [rfs]; exact h.jx.efs
  obtain ⟨op, hpre⟩ := smPre hP hwp (by omega) tsp tg tfs fm (rx15.trans h.jx.ex15) (rdf.trans h.jx.edf)
    (by rw [frd]; decide) fnr hz1 h.z1e h.pz64 hz2 h.pw64 h.wz (by omega) (by omega) hl1 hl2 (bud_pre h.jx.bud hrk)
  have hS := Ensures.toSummaryIn (hE b1 L1 op pz lz cz pw lw cw (nE s mp ml))
    (A64.noExit_restrict64 hap LibW.names) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide)
    (codeIn_NE hap libW_sub)
  rw [sm_a] at hS
  refine ReachesRet.call_regions hS f0 ⟨?ra, by rw [rx15]; exact h.jx.ex15, ?args, by rw [rdf]; exact h.jx.edf, hpre⟩
    (fun s' hr hq hrg => ?_)
  case ra => rw [tsp, fm, frd]; exact ra_ev hap libW_nf 1029 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨r0, r3, r1, r7, r6, r8, r9, r10, r11, trivial⟩
  obtain ⟨⟨e4, -, e14, ex15⟩, hq⟩ := hq
  obtain ⟨efs, edf, p3, l3, c3, g0, g3, g1, hv, hN, hlc, hc40, L2, b2, hx, hb, -, hinv, hlv, hor, hF, hLF, -⟩ := hq
  simp only [win, tsp, SubMod2N.K, SubMod2N.A] at hF
  rw [fm] at hF hLF hrg hv
  rw [hz1.2.2.1, hz2.2.2.1] at hv
  rw [tg] at hinv
  obtain ⟨qd, kd, hds, hdl, hdw, hF', hLF', hsb, ehd, hapd⟩ :=
    frm_dst hP hwp hz1 hx (stk := 4576) (above := 88) (by omega) (by omega) hF hLF
  obtain ⟨hw', hkc, hkeep⟩ := stepC hP hwp hds hdl hdw (stk := 4576) (above := 88) (by omega) (by omega) hF' hLF' hrg
    hx hinv hsb
  have hS4 : s'.regs 4 = S.regs 4 := by rw [e4, f4, h.jx.esp]; exact bv_add8 (by omega) (by omega)
  have hkk := kk_push2 hsp8 (by decide) hFp hkc
  have hjx := h.jx.call hS4 (e14.trans r14) (efs.trans rfs) (ex15.trans rx15) (edf.trans rdf) hw' hkk
    (bud_step h.jx.bud hrk hb)
  have hm1' := hkeep _ _ _ _ (hlnp _ _ _ _ h.m1) fun c0 => hapd _ _ c0 fun cz0 => (h.za1 cz0).symm
  have hm2' := hkeep _ _ _ _ (hlnp _ _ _ _ h.m2) fun c0 => hapd _ _ c0 fun cz0 => (h.za2 cz0).symm
  have hz2' := hkeep _ _ _ _ hz2 fun c0 => hapd _ _ c0 fun cz0 => h.wz c0 cz0
  have hzs' := LZ.step hP hwp (stk := 4576) (above := 88) (by omega) (by omega) hF' hLF' hx hsb hzsp
    fun c0 => hapd _ _ c0 fun cz0 => h.Zz1 c0 cz0
  have hp3 : p3 < 2 ^ 64 := by rw [← g0]; exact BitVec.isLt _
  have hz3 := LN.of_sm hP hwp hz1 hv hN hlc hc40 hlv hor hx hsb (fun _ hne => absurd ehd hne)
  have hH1 := (h.m1.1.2.1 h.c1p).2.1
  have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
  exact K10 s' L2 b2 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 ⟨hjx, by rw [hr, retAddrOf_eq, tsp, fm, frd],
    bv_of_toNat g0, bv_of_toNat g3, bv_of_toNat g1,
    by rw [kk_off hkk 0x118 8 (by decide) (by decide)]; exact h.s118,
    by rw [kk_off hkk 0xc8 8 (by decide) (by decide)]; exact h.sc8,
    by rw [kk_off hkk 0xd0 8 (by decide) (by decide)]; exact h.sd0,
    by rw [kk_off hkk 0x110 8 (by decide) (by decide)]; exact h.s110,
    by rw [kk_off hkk 0xb8 8 (by decide) (by decide)]; exact h.sb8,
    by rw [kk_off hkk 0xc0 8 (by decide) (by decide)]; exact h.sc0,
    by rw [kk_off hkk 0xf8 8 (by decide) (by decide)]; exact h.sf8,
    by rw [kk_off hkk 0x80 8 (by decide) (by decide)]; exact h.s80,
    by rw [kk_off hkk 0x88 8 (by decide) (by decide)]; exact h.s88,
    by rw [kk_off hkk 0x108 8 (by decide) (by decide)]; exact h.s108,
    by rw [kk_off hkk 0xa0 8 (by decide) (by decide)]; exact h.sa0,
    by rw [kk_off hkk 0xa8 8 (by decide) (by decide)]; exact h.sa8,
    hm1', h.c1p, hm2', h.ap, hz2', h.pw64, h.z2e, h.wa1, h.wa2, hzs', h.pZ64, h.Ze, h.Za1, h.Za2, h.Zz2, hz3, hp3,
    EL.of_res h.z1e hw.le hor,
    apart_res hor hH1 h.za1,
    apart_res hor (h.m2.1.2.1 ha2).2.1 h.za2,
    fun c0 cw0 => apart_res hor (h.z2.1.2.1 cw0).2.1 (fun cz0 => (h.wz cw0 cz0).symm) c0,
    fun c0 cZ0 => apart_res hor (h.zs.2.1 cZ0).2.1 (fun cz0 => (h.Zz1 cZ0 cz0).symm) c0⟩

end

end FvModexp.Amd64.ExpEven
