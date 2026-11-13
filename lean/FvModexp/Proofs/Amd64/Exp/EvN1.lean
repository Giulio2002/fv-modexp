import FvModexp.Proofs.Amd64.Exp.EvJ
import FvModexp.Proofs.Amd64.Exp.EvEnt
import FvModexp.Proofs.Amd64.Exp.EvTz
import FvModexp.Proofs.Amd64.Exp.EvCall
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): from the entry to the return of `m1 = stk.nat(n/64 + 1)` (`nat1R`) (asm s57; twin of
infra's arm64 `EvN1`)

`seg1` = `entA` (prologue) ∘ `tzLoop` (`n = tz M`) ∘ `entB` (defer record, `stk.nat` arguments) ∘ the call of
`(*stack).nat` (`StackNat.HypL`, `snCallE`); the continuation gets the join `J1` (context `WC` at level
`ℓ₀ + rnd(n/64 + 1)`, the slots `ESl`, `0xd8 = ml - n/64`, the scratch nat `m1`), the scratch fact `Scr` and `m1`'s
address.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

theorem bv_add8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 (sp - 8) + 8#64 = BitVec.ofNat 64 sp := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem bv_of_toNat {x : W64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the entry to `nat1R`** (see the module doc) -/
theorem seg1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true)
    (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (haN : aboveN ≤ 0x7f)
    (ret0 : W64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hkN : stkN ≤ K)
    (hM : 0 < natVal s.mem mp ml) (rk : Nat)
    (hbud : stackNatCost (stLen s.mem st) (a1 (nE s mp ml)) + rk ≤ b)
    (hl16 : stLen s.mem st + a1 (nE s mp ml) + 3 ≤ 2 ^ 16)
    (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zc) (h7 : s.regs 7 = BitVec.ofNat 64 st)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl) (h9 : s.regs 9 = BitVec.ofNat 64 xc)
    (K1 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p : Nat),
      J1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p →
      Scr R L L1 s.mem S.mem st p (a1 (nE s mp ml)) → p = stW S.mem st + 8 * stLen s.mem st →
      ReachesRet (LibNE.program.link impl) ret0 S Q) :
    ReachesRet (LibNE.program.link impl) ret0 s Q := by
  have hk := hP.kf
  have hP' := hP
  obtain ⟨⟨e4, e14, efs, ex15, edf, -, -, -, hce, -⟩, -, -, -, hml0, hml, -, -, -, -, -, -, -, -, -, -, hxl, hxp, hxc,
    hzp, hzc, -, -, hsok, hstw, -, -, -, -, -, -, -, -, -, hmo, hbpb, -⟩ := hP'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, -⟩ := hce
  obtain ⟨hmO, hmacc, hm48, -, -, hyp, hyc, hmp, hmcl, -⟩ := hmo
  obtain ⟨hbp5, hr0, -, ryp, ryl, ryc, rmp, rml, rmc⟩ := hbpb
  have hmc : mc < 2 ^ 64 := by have := hmcl.1; omega
  have hmw := hmO.2.1
  unfold Apart at hstw hmw
  have hst48 := hsok.2.2.2.1
  have hst24 := hsok.2.2.1
  have hXl : natVal s.mem mp ml < Exp.B ^ ml := by
    have := Janus.Arm64.Memory.readLE_lt s.mem mp (8 * ml)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
    rw [Exp.B_def, ← Nat.pow_mul, show 64 * ml = 8 * (8 * ml) by omega]; exact this
  have hXl' : natVal s.mem mp ml < 2 ^ (64 * ml) := by rw [Exp.B_def, ← Nat.pow_mul] at hXl; exact hXl
  have htz : nE s mp ml < 64 * ml := tz_lt hM hXl'
  have hbp : bp < 2 ^ 64 := by rw [← hbp5]; exact BitVec.isLt _
  have h5 : s.regs 5 = BitVec.ofNat 64 bp := bv_of_toNat hbp5
  refine entA ret0 Q sp g zp zc st xp xl xc mp ml bp s.mem (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)) c5 c6 (by omega) hml0 (by omega) hmp hbp hzp
    (by omega) hxp (by omega) hxc s hpc e4 h0 h1 h7 h6 h8 h9 h5 e14 rfl rml rmp ?_
  intro S1 M1 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 hF1 hrg1 q1 q2 q3 q4 q5 q6
  have hmr : ∀ j, j < ml → S1.mem.readLE ((BitVec.ofNat 64 mp).toNat + 8 * j) 8 = Exp.wd (natVal s.mem mp ml) j := by
    intro j hj
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmp, t12,
      hF1.readLE _ _ (by simp only [FW, outside_cons, outside_nil, and_true]; omega)]
    exact Expmc.readLE_wd _ _ _ _ hj
  refine tzLoop ret0 Q S1 (BitVec.ofNat 64 mp) ml (natVal s.mem mp ml) hmr
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmp, t12, hF1.accessible]; exact hmacc)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmp]; exact hm48) hM hXl t6 t5 ?_ (ml - 0) 0 S1 rfl
    (Nat.zero_le _) (fun j hj => absurd hj (by omega)) t1 ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩ t4
  intro S2 d1 ⟨d2, d3, d4, d5, d6⟩ d7
  have hl0 : M1.readLE (st + 8) 8 = stLen s.mem st :=
    hF1.readLE _ _ (by simp only [FW, outside_cons, outside_nil, and_true]; omega)
  refine entB ret0 Q sp g st ml (nE s mp ml) (stLen s.mem st) M1 (by omega) (by omega)
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega))
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ hst24) hst48 (by omega) hl0
    (by omega) (by omega) (by omega) S2 d1 ((d2 4 (by omega) (by omega)).trans t2) d7
    ((d2 7 (by omega) (by omega)).trans t7) ((d2 2 (by omega) (by omega)).trans t5)
    ((d2 14 (by omega) (by omega)).trans t8) (d3.trans t12) ?_
  intro S3 M3 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 hF3 hrg3 r1 r2 r3 r4 r5 r6 r7 r8
  -- the context at the call
  have hw1 := wc_init hP (M := M1) hF1 hrg1
  obtain ⟨hw3, -⟩ := WC.own hP hw1 hF3 hrg3 (fun r hr => by
    simp only [FB, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have tsp3 : (S3.regs 4).toNat = sp - 8 := by rw [f2, BitVec.toNat_ofNat]; omega
  have tg3 : (S3.regs 14).toNat = g := by rw [f6, BitVec.toNat_ofNat]; omega
  have tfs3 : S3.fsBase.toNat = fs := by rw [f7, d4, t9, efs]
  have hpre := snPre (stk := stkN) (above := aboveN) (n := a1 (nE s mp ml)) hP hw3 hkN (by omega) tsp3 tg3 tfs3 f10 (by simp only [a1]; omega)
    (by simp only [a1]; omega) (by omega)
  refine snCallE hap hns hsn (ra := nat1R) (ra_ev hap hnf 255 (by decide)) S3 (by rw [f1, stkNat_a])
    (by rw [tsp3, f10, r1]) (by omega) (by simp only [a1]; omega) f3 f4 (by rw [f8, d5, t10, ex15])
    (by rw [f9, d6, t11, edf]) hpre ?_
  intro S4 g1 g2 g3 g4 g5 g6 hpost
  have hS4 : S4.regs 4 = BitVec.ofNat 64 sp := by rw [g2, f2]; exact bv_add8 (by omega) (by omega)
  obtain ⟨L2, b2, hb2, hw4, hsc, hz0, hz1, hz2, hfs4, hdf4, hF, -, -, -, -⟩ :=
    WC.stkNat hP hw3 hkN (by omega) tsp3 tg3 f10 (g6.trans (by rw [f10])) (by simp only [a1]; omega) hpost
  have hkc := keepC hP hw3 (zs := []) (by simpa only [List.append_nil] using hF) hkN (by omega)
    (fun _ _ _ _ => by simp only [outside_nil])
  have kp : ∀ a, sp + 0x77 ≤ a → a + 8 ≤ sp + 0x1b8 → S4.mem.readLE a 8 = M3.readLE a 8 := fun a h1 h2 =>
    hkc a 8 (by omega) h2
  have hB : ∀ a, (sp + 0x140 ≤ a ∧ a + 8 ≤ sp + 0x198 ∨ sp + 0x1a0 ≤ a) →
      M3.readLE a 8 = M1.readLE a 8 := fun a ha =>
    hF3.readLE _ _ (by simp only [FB, outside_cons, outside_nil, and_true]; omega)
  have hA : ∀ a, sp + 0x148 ≤ a → a + 8 ≤ sp + 0x180 → M1.readLE a 8 = s.mem.readLE a 8 := fun a h1 h2 =>
    hF1.readLE _ _ (by simp only [FW, outside_cons, outside_nil, and_true]; omega)
  refine K1 S4 L2 b2 _ ⟨⟨hS4, g4.trans f6, by rw [hfs4, tfs3], by rw [g5, f8, d5, t10, ex15],
    by rw [hdf4, f9, d6, t11, edf], hw4, ?_, by omega⟩, g1, hz0, hz1, hz2,
    by rw [kp _ (by omega) (by omega), r4], ?_⟩ hsc rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kp _ (by omega) (by omega), hB _ (by omega)]; exact q1
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact hr0
    · rw [kp _ (by omega) (by omega)]; exact r8
    · rw [kp _ (by omega) (by omega)]; exact r5
    · rw [kp _ (by omega) (by omega)]; exact r6
    · rw [kp _ (by omega) (by omega)]; exact r7
    · rw [kp _ (by omega) (by omega), hB _ (by omega)]; exact q2
    · rw [kp _ (by omega) (by omega), hB _ (by omega)]; exact q3
    · rw [kp _ (by omega) (by omega)]; exact r2
    · rw [kp _ (by omega) (by omega), hB _ (by omega)]; exact q4
    · rw [kp _ (by omega) (by omega), hB _ (by omega)]; exact q5
    · rw [kp _ (by omega) (by omega), hB _ (by omega)]; exact q6
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact ryp
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact ryl
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact ryc
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact rmp
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact rml
    · rw [kp _ (by omega) (by omega), hB _ (by omega), hA _ (by omega) (by omega)]; exact rmc
    · rw [kp _ (by omega) (by omega)]; exact r3
  · exact DL.of_scr hw4 hsc rfl (by have := rnd_ge (a1 (nE s mp ml)); omega) (by simp only [a1]; omega)

end FvModexp.Amd64.ExpEven
