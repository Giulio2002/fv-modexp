import FvModexp.Proofs.Arm64.Top.RunC2EX
import FvModexp.Proofs.Common.GenReg

set_option autoImplicit false

/-! # `Run` (arm64): `C2` to `V` when `base ≠ 1` (`base.BitLen() ≠ 1`): to the `exp` call block, then `RunC2EX` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem le_or_left' {a b c : Nat} (h : a ≤ b) : a ≤ b ||| c := Nat.le_trans h Nat.left_le_or

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c2e (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hE : RunIface.ExpSpec impl R stkM aboveM) (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (Q : Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 28).toNat + 16) 8 L)
    (hbB : okB s p len ≤ b) (hone : FvModexp.Spec.RunArm64.NatOne R s.mem (win s W 40))
    (hpool : FvModexp.Spec.RunArm64.StackPool R s.mem (win s W 40))
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 L1 b1 T)
    (hpc : T.pc = BitVec.ofNat 64 pcC2) (h7 : T.regs 7 = 64#64)
    (hv0 : opV s p len 0 ≠ 1) (hv2 : 0 < opV s p len 2)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.pc = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have hX := c2eX impl hap R stkM aboveM hE hBy hsv b L c p len cp ret hret s Q W henvW hW hW1 hab hglob hgL hbB hone hpool L1 b1
  have hrel0 := hrel
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henvW
  obtain ⟨hsp, h28, h29, h18, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hMF, -, hop, -⟩ := hrel
  simp only [stk] at hMF
  have hspn : T.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  obtain ⟨-, hval0, hnorm0, h1280, hlc0, hlive0⟩ := hop 0 (by omega)
  clear hop
  simp only [opAt, natAt, show s.sp.toNat - 136 - 32 * 0 + 8 = s.sp.toNat - 128 by omega,
    show s.sp.toNat - 128 + 8 = s.sp.toNat - 120 by omega,
    show s.sp.toNat - 136 - 32 * 0 + 16 = s.sp.toNat - 120 by omega,
    show s.sp.toNat - 136 - 32 * 0 + 24 = s.sp.toNat - 112 by omega] at hval0 hnorm0 h1280 hlc0 hlive0
  generalize hmpd : T.mem.readLE (s.sp.toNat - 128) 8 = mp at hval0 hnorm0 hlive0
  generalize hmld : T.mem.readLE (s.sp.toNat - 120) 8 = ml at hval0 hnorm0 h1280 hlc0
  rcases Nat.eq_zero_or_pos ml with h0 | hml1
  · -- `len(base.abs) = 0`: `bitLen` is `0`
    subst h0
    janus_run [hmld] until [segAddr Extracted.program fn + 0x864]
    exact hX _ (RelD.congr hrel0 (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp))
      (by janus_simp) hv2 hk
  · have hq := msb_sub_one_le ml hml1 (by omega)
    have hmp : mp < 2 ^ 64 := by rw [← hmpd]; exact Memory.readLE_lt _ _ 8
    obtain ⟨-, -, hpacc, hp48, -, -⟩ := hlive0 (by omega)
    have hA : T.mem.accessible mp (8 * ml) false = true := by
      rw [hMF.accessible]; exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
    have ht : T.mem.readLE (mp + 8 * (ml - 1)) 8 ≠ 0 := hnorm0.resolve_left (by omega)
    janus_run [hmpd, hmld, hq] until [segAddr Extracted.program fn + 0x818]
    generalize hxd : BitVec.ofNat 64 (T.mem.readLE (mp + 8 * (ml - 1)) 8) = x
    janus_run [h7] until [segAddr Extracted.program fn + 0x844]
    gen_reg 5 as bl with hBl
    have hx0 : 0 < x.toNat := by rw [← hxd]; exact toNat_ofNat_readLE_pos _ _ ht
    have hbl1 : bl.toNat ≠ 1 := by
      intro h1
      rw [← hBl] at h1
      obtain ⟨hm1, hx1⟩ := (blr_one x.toNat _ ml hx0 (by (repeat apply le_or_left'); exact Nat.le_refl _)
        (fun h => by have := BitVec.eq_of_toNat_eq (y := 1#64) h; subst this; decide)
        (by repeat (first | apply Nat.or_lt_two_pow | exact BitVec.isLt _)) hml1 (by omega)).1 h1
      subst hm1
      rw [← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Memory.readLE_lt _ _ 8)] at hx1
      apply hv0
      rw [← hval0, natVal_succ, natVal_zero, show mp + 8 * 0 = mp + 8 * (1 - 1) by rfl, hx1]
    have hb1 : (bl = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro h; apply hbl1; rw [h]; rfl
    janus_run [hb1] until [segAddr Extracted.program fn + 0x864]
    exact hX _ (RelD.congr hrel0 (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp))
      (by janus_simp) hv2 hk

end FvModexp.Arm64.Run
