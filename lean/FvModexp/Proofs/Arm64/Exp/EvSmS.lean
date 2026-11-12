import FvModexp.Proofs.Arm64.Exp.EvSm

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): **`segSm`** — `J9` (`mvJ`) → `z1 = z1.subMod2N(z1, z2, n)` → `J10` (`smR`) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

/-- a value below `2^n` (`n < 64 ml`) or below the modulus has at most `ml ≤ 2^12` limbs -/
theorem len_bdE {M : Memory} {p l ml v : Nat} (hN : NatNorm M p l) (hv : natVal M p l = v) (hlt : v < 2 ^ (64 * ml))
    (hml : ml ≤ 128) : l ≤ 2 ^ 12 := by
  have := nlen_bd' hN (by rw [hv]; exact hlt); omega

theorem natVal_lt64 (m : Memory) (p l : Nat) : natVal m p l < 2 ^ (64 * l) := by
  have := Memory.readLE_lt m p (8 * l)
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * l) = 64 * l by omega] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`J9` → `J10`** (see EvSm's module doc) -/
theorem segSm {impl : List Segment} (hap : ImplApart Extracted.program impl) (hE : SubMod2N.EnsG impl R)
    (hK4 : 4608 ≤ K) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) {rk rk' : Nat} (hrk : SubMod2N.costG (nE s mp ml) + rk' ≤ rk)
    {ret0 : BitVec 64} {Q : State → Prop}
    (K10 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 : Nat),
      J10 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk' S L1 b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 →
      ReachesRet (LibNE.program.link impl) ret0 S Q)
    {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : J9 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  obtain ⟨hn0, hnl⟩ := nE_bd hP hM hev
  have hw := h.jx.wc
  have hb1 := h.jx.bud
  have hsN : S.sp.toNat = sp := by rw [h.jx.esp, BitVec.toNat_ofNat]; omega
  have hacc : S.mem.accessible (sp + 128) 320 false = true := by
    rw [hw.fr.accessible]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc0 (by omega) (by omega))
  have h184 : S.mem.readLE (sp + 184) 8 = nE s mp ml := h.jx.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
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
  refine runSm ret0 Q sp pz lz cz (nE s mp ml) S.mem hal hsp2 hacc h.s152 h.s264 h.s160 h184 S h.pc h.jx.esp rfl ?_
  intro S' f0 fsp fm r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r30 r18 r28 r29
  obtain ⟨op, hpre⟩ := smPre hP hw hK4 (fsp.trans h.jx.esp) (r28.trans h.jx.e28) fm r30 ⟨by decide, by decide⟩
    h.z1 h.z1e h.pz64 h.z2 h.pw64 h.wz (by omega) (by omega) hl1 hl2 (bud_pre hb1 hrk)
  have hS := CallNE.hypSum hap libW_sub (hE b1 L1 op pz lz cz pw lw cw (nE s mp ml))
  have hsN' : S'.sp.toNat = sp := by rw [fsp]; exact hsN
  refine ReachesRet.call_regions hS (by rw [f0, show segAddr Extracted.program SubMod2N.fn = 1805584 by decide]) ⟨?_, ?_, hpre⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [r30, LibCalls.tN (by simp only [smR]; omega)]; exact ra_ev hap libW_nf 165 (by decide)
  · simp only [ArgsFrom]
    exact ⟨r0, r1, r2, r3, r4, r5, r6.trans h.r0, r7.trans h.r4, r8.trans h.r2, r9, trivial⟩
  · obtain ⟨p3, l3, c3, g0, g1, g2, hv, hN, hlc, hc40, L2, b2, hx, hb, -, hinv, hlv, hor, hF, hLF, -⟩ := hq
    simp only [winA, hsN', SubMod2N.K, SubMod2N.A] at hF
    rw [fm] at hF hLF hrg hv
    rw [h.z1.2.2.1, h.z2.2.2.1] at hv
    rw [r28, h.jx.e28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hP.1.2.2.1; omega)] at hinv
    obtain ⟨qd, kd, hds, hdl, hdw, hF', hLF', hsb, ehd, hapd⟩ :=
      frm_dst hP hw h.z1 hx (stk := 4608) (above := 88) hK4 (by omega) hF hLF
    obtain ⟨hw', hk, hkeep⟩ := stepC0 hP hw hds hdl hdw (stk := 4608) (above := 88) hK4 (by omega) hF' hLF' hrg
      hx hinv hsb
    have hjx := h.jx.call (e1.trans fsp) (e2.trans r28) (e3.trans r29) (e4.trans r18) hw' hk (by omega)
      (bud_step hb1 hrk hb)
    have hm1' := hkeep _ _ _ _ h.m1 fun c0 => hapd _ _ c0 fun cz0 => (h.za1 cz0).symm
    have hm2' := hkeep _ _ _ _ h.m2 fun c0 => hapd _ _ c0 fun cz0 => (h.za2 cz0).symm
    have hz2' := hkeep _ _ _ _ h.z2 fun c0 => hapd _ _ c0 fun cz0 => h.wz c0 cz0
    have hzs' := LZ.step hP hw (stk := 4608) (above := 88) hK4 (by omega) hF' hLF' hx hsb h.zs
      fun c0 => hapd _ _ c0 fun cz0 => h.Zz1 c0 cz0
    have hp3 : p3 < 2 ^ 64 := by rw [← g0]; exact BitVec.isLt _
    have hz3 := LN.of_sm hP hw h.z1 hv hN hlc hc40 hlv hor hx hsb (fun _ hne => absurd ehd hne)
    have hH1 := (h.m1.1.2.1 h.c1p).2.1
    have k288 := hk (sp + 288) 8 (Or.inr ⟨by omega, by omega⟩)
    have k208 := hk (sp + 208) 8 (Or.inr ⟨by omega, by omega⟩)
    have k216 := hk (sp + 216) 8 (Or.inr ⟨by omega, by omega⟩)
    have k280 := hk (sp + 280) 8 (Or.inr ⟨by omega, by omega⟩)
    have k192 := hk (sp + 192) 8 (Or.inr ⟨by omega, by omega⟩)
    have k200 := hk (sp + 200) 8 (Or.inr ⟨by omega, by omega⟩)
    have k256 := hk (sp + 256) 8 (Or.inr ⟨by omega, by omega⟩)
    have k136 := hk (sp + 136) 8 (Or.inr ⟨by omega, by omega⟩)
    have k144 := hk (sp + 144) 8 (Or.inr ⟨by omega, by omega⟩)
    have k272 := hk (sp + 272) 8 (Or.inr ⟨by omega, by omega⟩)
    have k168 := hk (sp + 168) 8 (Or.inr ⟨by omega, by omega⟩)
    have k176 := hk (sp + 176) 8 (Or.inr ⟨by omega, by omega⟩)
    have ha2 : 0 < a2 ml (nE s mp ml) := by simp only [a2]; omega
    exact K10 s' L2 b2 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 ⟨hjx, hr.trans r30,
      BitVec.eq_of_toNat_eq (by rw [g0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp3]),
      BitVec.eq_of_toNat_eq (by rw [g1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
      BitVec.eq_of_toNat_eq (by rw [g2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]),
      by rw [k288]; exact h.s288, by rw [k208]; exact h.s208, by rw [k216]; exact h.s216,
      by rw [k280]; exact h.s280, by rw [k192]; exact h.s192, by rw [k200]; exact h.s200,
      by rw [k256]; exact h.s256, by rw [k136]; exact h.s136, by rw [k144]; exact h.s144,
      by rw [k272]; exact h.s272, by rw [k168]; exact h.s168, by rw [k176]; exact h.s176,
      hm1', h.c1p, hm2', h.ap, hz2', h.pw64, h.wa1, h.wa2, hzs', h.pZ64, h.Za1, h.Za2, h.Zz2, hz3, hp3,
      apart_res hor hH1 h.za1,
      apart_res hor (h.m2.1.2.1 ha2).2.1 h.za2,
      fun c0 cw0 => apart_res hor (h.z2.1.2.1 cw0).2.1 (fun cz0 => (h.wz cw0 cz0).symm) c0,
      fun c0 cZ0 => apart_res hor (h.zs.2.1 cZ0).2.1 (fun cz0 => (h.Zz1 cZ0 cz0).symm) c0⟩

end

end FvModexp.Arm64.ExpEven
