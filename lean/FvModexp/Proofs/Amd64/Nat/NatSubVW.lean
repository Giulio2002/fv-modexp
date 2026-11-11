import FvModexp.Proofs.Amd64.Nat.NatSubTail
import FvModexp.Proofs.Amd64.Nat.SubVW
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.sub` (amd64): after `subVV.abi0` (`+0x189`): `XORPS X15; MOVQ FS:-8, R14`, then
`if m > n { c = subVW(z[n:], x[n:], c) }`, then the tail. The carry is in `0x48(RSP') = RSP - 72`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem afterVV (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hxc : xl.toNat ≤ xc.toNat) (hxc63 : xc.toNat < 2 ^ 63)
    (hps : M.readLE ((s.regs 4).toNat - 24) 8 = p) (hcs : M.readLE ((s.regs 4).toNat - 56) 8 = c)
    (hms : M.readLE ((s.regs 4).toNat - 64) 8 = xl.toNat)
    (hlo : natVal M p yl.toNat + natVal s.mem yp.toNat yl.toNat =
      natVal s.mem xp.toNat yl.toNat + 2 ^ (64 * yl.toNat) * M.readLE ((s.regs 4).toNat - 72) 8)
    (hb1 : M.readLE ((s.regs 4).toNat - 72) 8 ≤ 1)
    (hge : natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat)
    (hhi : natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
      natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hAfterVV)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  have hc2 : CodeIn64 ((Extracted.program.onlySegments [SubVW.fn]).link impl) (LibNatSub.program.link impl) := by
    rw [LibNatSub.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hVW' := fun b L => Ensures.toSummaryRegs7 (fun zp zl zc xp xl xc y => SubVW.ens impl hap R hmv b L zp zl zc xp xl xc y)
    (A64.noExit_restrict64 hap [SubVW.fn]) hc2
  clear hc2
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hyl := h.yl40
  have r1 := h.sxl; have r2 := h.syl; have r3 := h.sxc; have r4 := h.sxp
  have hsacc := h.sacc; have hal := h.al; have htls := h.tls; have htacc := h.tacc
  have htb := h.tlsg.base
  have hcw := Janus.Arm64.Memory.readLE_lt M ((s.regs 4).toNat - 72) 8
  by_cases hxy : yl.toNat = xl.toNat
  · have hge' : natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat yl.toNat := by
      have := hge; rw [← hxy] at this; exact this
    obtain ⟨hb0, hlo'⟩ := sub_one_piece hlo (natVal_lt M p yl.toNat) hb1 hge'
    janus64_run [hm, r1, r2, hps, hcs, hms, htls, hfs, hb0, BitVec.msb_eq_decide,
      (show (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 by omega)] until [hTail]
    refine tail impl R b L zp zc xp xl xc yp yl s p c L' b' M h hps hms hcs (by rw [← hxy, hlo']) _ rfl
      ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals try janus64_simp
    all_goals first | exact h.x15.symm | exact hdf | exact h.df0 | skip
  · have hlt : yl.toNat < xl.toNat := by omega
    have e1 : ((0#64 - (BitVec.ofNat 64 c - yl)).sshiftRight 63 &&& yl <<< 3) = yl <<< 3 :=
      neg_sshr63_and _ _ (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    have e2 : ((0#64 - (xc - yl)).sshiftRight 63 &&& yl <<< 3) = yl <<< 3 :=
      neg_sshr63_and _ _ (by simp only [BitVec.toNat_sub]; omega) (by simp only [BitVec.toNat_sub]; omega)
    have hpw := h.pw; have hpg := h.pg; have hpf := h.pf; have hxw := h.xw; have hgw := h.gw; have hgok := h.gok
    have htw := h.tw
    unfold Apart at hpw hpg hpf hxw hgw htw
    have hzh2 : InRanges (yl.toNat * 8 + p) (8 * (xl.toNat - yl.toNat)) L' ∨
        Outside (yl.toNat * 8 + p) (8 * (xl.toNat - yl.toNat)) R.rt := h.pheld.sub (by omega) (by omega)
    have hzb1 : M.accessible (p + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) true = true :=
      Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
    have hxb : M.accessible (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) false = true :=
      Janus.Arm64.Memory.accessible_mono _ h.xacc (by omega) (by omega)
    have hxh2 : InRanges (xp.toNat + yl.toNat * 8) (8 * (xl.toNat - yl.toNat)) L' ∨
        Outside (xp.toNat + yl.toNat * 8) (8 * (xl.toNat - yl.toNat)) R.rt := h.xheld.sub (by omega) (by omega)
    have hzx3 : yl <<< 3 + BitVec.ofNat 64 p = xp + yl <<< 3 ∨
        Apart (yl.toNat * 8 + p) (8 * (xl.toNat - yl.toNat)) (xp.toNat + yl.toNat * 8) (8 * (xl.toNat - yl.toNat)) := by
      rcases h.px with e | e
      · left; rw [show BitVec.ofNat 64 p = xp from BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt xp.isLt]), BitVec.add_comm]
      · right; unfold Apart at e ⊢; omega
    have hLsW : ∀ r ∈ L', r.fst + (r.snd - r.fst) ≤ (s.regs 4).toNat - 152 - 4136 ∨ (s.regs 4).toNat - 152 + 40 ≤ r.fst := by
      intro r hr; have := h.lsep r hr; simp only [Outside, and_true] at this; omega
    have hmv2 : ∀ j, 1 ≤ j → j ≤ xl.toNat - yl.toNat →
        R.ok (cA "runtime.memmove")
          [if j < c - yl.toNat then yl.toNat * 8 + p + 8 * j else yl.toNat * 8 + p,
            if j < xc.toNat - yl.toNat then xp.toNat + yl.toNat * 8 + 8 * j else xp.toNat + yl.toNat * 8,
            8 * (xl.toNat - yl.toNat - j)] := fun j _ _ => h.mv _ _ _ (by omega)
    have hinv := h.inv; have hgrd := h.grd; have hgacc := h.gacc; have hg48 := h.g48; have hwrt := h.wrt
    have hgrt := h.grt; have hp8 := h.p8; have hx48 := h.x48; have htrt := h.trt; have hra := h.ra47
    janus64_run [hm, r1, r2, r3, r4, hps, hcs, hms, htls, hfs, BitVec.msb_eq_decide, e1, e2,
      (show (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 by omega),
      sub_mod64 yl.toNat xl.toNat (by omega) xl.isLt, sub_mod64 yl.toNat xc.toNat (by omega) xc.isLt,
      sub_mod64 yl.toNat c (by omega) (by omega), mod64_of_lt c (by omega), mod64_of_lt (p + 8 * yl.toNat) (by omega),
      mod64_of_lt (xp.toNat + 8 * yl.toNat) (by omega)] until [hTail] calls [hVW']
    rename_i _ _ _ _ _ hfs2 _ L2 b2 hext hbb hc0 hv2 hinv2 hF2 hLF2
    have e152 : (s.regs 4 - 152#64).toNat = (s.regs 4).toNat - 152 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have ea : yl.toNat * 8 + p = p + 8 * yl.toNat := by omega
    have eb : xp.toNat + yl.toNat * 8 = xp.toNat + 8 * yl.toNat := by omega
    rw [ea] at hv2 hF2 hLF2
    rw [eb] at hv2 hc0
    have hm1 := h.frame0 (M2 := M.writeLE ((s.regs 4).toNat - 152) 8 6183677) (ws := [((s.regs 4).toNat - 152, (s.regs 4).toNat - 144)]) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp only; omega)
      (by janus_frame)
    have hF3 : MemFrame (M.writeLE ((s.regs 4).toNat - 152) 8 6183677) s'.mem (R.rt ++ [((s.regs 4).toNat - 4288, (s.regs 4).toNat - 112),
        (p + 8 * yl.toNat, p + 8 * yl.toNat + 8 * (xl.toNat - yl.toNat))]) := by
      refine hF2.mono fun a n ho => ?_
      simp only [win, Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152, outside_append, outside_cons, outside_nil,
        and_true] at ho ⊢
      obtain ⟨hr, c1, c3⟩ := ho
      exact ⟨⟨hr, by omega⟩, c3⟩
    have hws : WsOK s p c [((s.regs 4).toNat - 4288, (s.regs 4).toNat - 112),
        (p + 8 * yl.toNat, p + 8 * yl.toNat + 8 * (xl.toNat - yl.toNat))] := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    have hM2 := hm1.frame hws hF3 (LiveFrame.mono_ws hLF2 fun a n ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.2) hext hbb hinv2
    have rd : ∀ a, (s.regs 4).toNat - 112 ≤ a → a + 8 ≤ (s.regs 4).toNat + 80 → (a + 8 ≤ (s.regs 4).toNat - 152 ∨ (s.regs 4).toNat - 144 ≤ a) →
        s'.mem.readLE a 8 = M.readLE a 8 := by
      intro a h1 h2 h3
      rw [hm1.read hF3 (by omega) h2 (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)]
      exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    have hpw := h.pw; unfold Apart at hpw
    have hlow : natVal s'.mem p yl.toNat = natVal M p yl.toNat := by
      unfold natVal
      rcases h.pheld.sub (a := p) (n := 8 * yl.toNat) (Nat.le_refl _) (by omega) with hin | hout
      · rw [hLF2.readLE _ _ hin (by simp only [outside_cons, outside_nil, and_true]; omega)]
        exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
      · rw [hF3.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hout, by omega, by omega⟩)]
        exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    have hc0' : (s'.regs 0).toNat = if xl.toNat - yl.toNat = 0 then M.readLE ((s.regs 4).toNat - 72) 8 else
        if natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) < M.readLE ((s.regs 4).toNat - 72) 8 then 1 else 0 := hc0
    have hv2'' : natVal s'.mem (p + 8 * yl.toNat) (xl.toNat - yl.toNat) =
        (natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) + 2 ^ (64 * (xl.toNat - yl.toNat)) -
          M.readLE ((s.regs 4).toNat - 72) 8) % 2 ^ (64 * (xl.toNat - yl.toNat)) := hv2
    have hsp := natVal_add s'.mem p yl.toNat (xl.toNat - yl.toNat)
    have hsx := natVal_add s.mem xp.toNat yl.toNat (xl.toNat - yl.toNat)
    rw [Nat.add_sub_cancel' hyx] at hsp hsx
    have hHlt := natVal_lt s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat)
    obtain ⟨hcH, hmodk, hsum⟩ := sub_two_piece hlo (natVal_lt M p yl.toNat) hb1 hHlt (by rw [← hsx]; exact hge)
      (Nat.pow_pos (by omega))
    have hv2' : natVal s'.mem (p + 8 * yl.toNat) (xl.toNat - yl.toNat) =
        natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) - M.readLE ((s.regs 4).toNat - 72) 8 := by
      rw [hv2'', hhi, hmodk]
    have hval : natVal s'.mem p xl.toNat = natVal s.mem xp.toNat xl.toNat - natVal s.mem yp.toNat yl.toNat := by
      rw [hsp, hlow, hv2', hsum, hsx]
    have hr0 : s'.regs 0 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [hc0', hhi, if_neg (by omega), if_neg (by omega)]; rfl
    refine tail impl R b L zp zc xp xl xc yp yl s p c L2 b2 s'.mem hM2
      ((rd _ (by omega) (by omega) (by omega)).trans hps) ((rd _ (by omega) (by omega) (by omega)).trans hms)
      ((rd _ (by omega) (by omega) (by omega)).trans hcs) hval _ rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals try janus64_simp
    all_goals first | exact h.x15.symm | exact hfs2 | exact hdf | exact h.df0 | skip

end FvModexp.Amd64.NatSub
