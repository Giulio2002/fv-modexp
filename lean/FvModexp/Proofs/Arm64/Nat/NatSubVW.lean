import FvModexp.Proofs.Arm64.Nat.NatSubTail
import FvModexp.Proofs.Arm64.Nat.SubVW
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.sub` (arm64): after `subVV` (`+0x104`): `if m > n { c = subVW(z[n:], x[n:], c) }`, then the tail

At `+0xbc` the carry of `addVV` is in `80(RSP') = SP - 80`, `z[:n] = (X_lo + Y) mod B^n` and `x[n:m]` still holds `X_hi`.
`m = n`: straight to the tail (`+0x11c`). `m > n`: the slice expressions `z[n:m]`, `x[n:]` (masked pointers, caps
`c - n`, `xc - n`), the call (`subVW`, `stk 4144`, `above 40` at `SP' = SP - 160`), then the tail.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatSub

-- (hAfterVV defined in NatAddTail)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem afterVV (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hxc : xl.toNat ≤ xc.toNat) (hxc63 : xc.toNat < 2 ^ 63)
    (hps : M.readLE (s.sp.toNat - 24) 8 = p) (hcs : M.readLE (s.sp.toNat - 56) 8 = c)
    (hms : M.readLE (s.sp.toNat - 64) 8 = xl.toNat)
    (hlo : natVal M p yl.toNat + natVal s.mem yp.toNat yl.toNat =
      natVal s.mem xp.toNat yl.toNat + 2 ^ (64 * yl.toNat) * M.readLE (s.sp.toNat - 80) 8)
    (hb1 : M.readLE (s.sp.toNat - 80) 8 ≤ 1)
    (hge : natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat)
    (hhi : natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
      natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hAfterVV)
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibNatSub.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s' := by
  have hc2 : CodeIn ((Extracted.program.onlySegments [SubVW.fn]).link impl) (LibNatSub.program.link impl) := by
    rw [LibNatSub.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hVW' := fun b L => Ensures.toSummaryRegs7 (fun zp zl zc xp xl xc y => SubVW.ens impl hap R hmv b L zp zl zc xp xl xc y) (noExit_restrict hap [SubVW.fn]) hc2
  clear hc2
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hyl := h.yl40
  have r1 := h.sxl; have r2 := h.syl; have r3 := h.sxc; have r4 := h.sxp
  have hsacc := h.sacc; have hal := h.al
  have hcw := Memory.readLE_lt M (s.sp.toNat - 80) 8
  by_cases hxy : yl.toNat = xl.toNat
  · -- `m = n`: no `subVW`
    have hge' : natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat yl.toNat := by
      have := hge; rw [← hxy] at this; exact this
    obtain ⟨hb0, hlo'⟩ := sub_one_piece hlo (natVal_lt M p yl.toNat) hb1 hge'
    janus_run [hm, r1, r2, hps, hcs, hb0] until [hTail]
    refine tail impl R b L zp zc xp xl xc yp yl s p c L' b' M h hps hms hcs (by rw [← hxy, hlo']) _ rfl
      ?_ ?_ ?_ ?_ h18 rfl
    all_goals janus_simp
  · have hlt : yl.toNat < xl.toNat := by omega
    have hm1 : ((yl - BitVec.ofNat 64 c).sshiftRight 63).toNat = 18446744073709551615 :=
      sshr63_of_lt _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
    have hm2 : ((yl - xc).sshiftRight 63).toNat = 18446744073709551615 := sshr63_of_lt _ _ (by omega) (by omega)
    have hand : yl.toNat &&& 18446744073709551615 = yl.toNat := and_ones64 _ yl.isLt
    -- the callee's precondition, piece by piece
    have hpw := h.pw; have hpg := h.pg; have hxw := h.xw; have hgw := h.gw; have hgok := h.gok
    unfold Apart at hpw hpg hxw hgw
    have hzh2 : Held R L' (p + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) := h.pheld.sub (by omega) (by omega)
    have hzb1 : M.accessible (p + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) true = true :=
      Memory.accessible_mono _ h.pacc (by omega) (by omega)
    have hxb : M.accessible (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) false = true :=
      Memory.accessible_mono _ h.xacc (by omega) (by omega)
    have hxh2 : Held R L' (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) := h.xheld.sub (by omega) (by omega)
    have hzx2 : p + 8 * yl.toNat = xp.toNat + 8 * yl.toNat ∨
        Apart (p + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) := by
      rcases h.px with e | e
      · left; omega
      · right; unfold Apart at e ⊢; omega
    have hLsW : ∀ r ∈ L', r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 160 - 4144 ∨ s.sp.toNat - 160 + 40 ≤ r.fst := by
      intro r hr; have := h.lsep r hr; simp only [Outside, and_true] at this; omega
    have hmv : ∀ (a d : BitVec 64) (zl zc xc' : Nat), zl ≤ xl.toNat →
        (if a = d then True else VWMoves R a.toNat zl zc d.toNat xc') := by
      intro a d zl zc xc' hz
      split
      · trivial
      · intro j _ _; exact h.mv _ _ _ (by omega)
    have e1 : (yl &&& (yl - BitVec.ofNat 64 c).sshiftRight 63) = yl :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and, hm1, hand])
    have e2 : (yl &&& (yl - xc).sshiftRight 63) = yl := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and, hm2, hand])
    have hzx3 : BitVec.ofNat 64 p + yl <<< 3 = xp + yl <<< 3 ∨
        Apart (p + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) := by
      rcases h.px with e | e
      · left; rw [show BitVec.ofNat 64 p = xp from BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt xp.isLt])]
      · right; unfold Apart at e ⊢; omega
    have hmv2 : ∀ j, 1 ≤ j → j ≤ xl.toNat - yl.toNat →
        R.ok (cA "runtime.memmove")
          [if j < c - yl.toNat then p + 8 * yl.toNat + 8 * j else p + 8 * yl.toNat,
            if j < xc.toNat - yl.toNat then xp.toNat + 8 * yl.toNat + 8 * j else xp.toNat + 8 * yl.toNat,
            8 * (xl.toNat - yl.toNat - j)] := fun j _ _ => h.mv _ _ _ (by omega)
    clear hzx2 hmv
    have hinv := h.inv; have hgrd := h.grd; have hgacc := h.gacc; have hg48 := h.g48; have hwrt := h.wrt
    have hgrt := h.grt; have hp8 := h.p8; have hx48 := h.x48
    -- the `% 2^64` facts go to the run only (in the context they make every `omega` call slow)
    janus_run [hm, r1, r2, r3, r4, hps, hcs, hms, hm1, hm2, hand, e1, e2,
      sub_mod64 yl.toNat xl.toNat (by omega) xl.isLt, sub_mod64 yl.toNat xc.toNat (by omega) xc.isLt,
      sub_mod64 yl.toNat c (by omega) (by omega), mod64_of_lt c (by omega), mod64_of_lt (p + 8 * yl.toNat) (by omega),
      mod64_of_lt (xp.toNat + 8 * yl.toNat) (by omega)] until [hTail] calls [hVW']
    rename_i _ _ _ _ _ L2 b2 hext hbb hc0 hv2 hinv2 hF2 hLF2
    have e160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hF3 : MemFrame M s'.mem (R.rt ++ [(s.sp.toNat - 4304, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 120),
        (p + 8 * yl.toNat, p + 8 * yl.toNat + 8 * (xl.toNat - yl.toNat))]) := by
      refine hF2.mono fun a n ho => ?_
      simp only [winA, e160, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, c1, c2, c3⟩ := ho
      exact ⟨⟨hr, by omega, by omega⟩, c3⟩
    have hws : WsOK s p c [(s.sp.toNat - 4304, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 120),
        (p + 8 * yl.toNat, p + 8 * yl.toNat + 8 * (xl.toNat - yl.toNat))] := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega
    have hM2 := h.frame hws hF3 (LiveFrame.mono_ws hLF2 fun a n ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.2.2) hext hbb hinv2
    have rd : ∀ a, s.sp.toNat - 120 ≤ a → a + 8 ≤ s.sp.toNat + 80 → s'.mem.readLE a 8 = M.readLE a 8 :=
      fun a h1 h2 => h.read hF3 (by omega) h2 (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
    -- the value
    have hlow : natVal s'.mem p yl.toNat = natVal M p yl.toNat :=
      Held.readLE2 (h.pheld.sub (Nat.le_refl _) (by omega)) hF2 hLF2
        (by simp only [winA, e160, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hsp := natVal_add s'.mem p yl.toNat (xl.toNat - yl.toNat)
    have hsx := natVal_add s.mem xp.toNat yl.toNat (xl.toNat - yl.toNat)
    rw [Nat.add_sub_cancel' hyx] at hsp hsx
    have hHlt := natVal_lt s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat)
    obtain ⟨hcH, hmodk, hsum⟩ := sub_two_piece hlo (natVal_lt M p yl.toNat) hb1 hHlt (by rw [← hsx]; exact hge)
      (Nat.pow_pos (by omega))
    have hv2' : natVal s'.mem (p + 8 * yl.toNat) (xl.toNat - yl.toNat) =
        natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) - M.readLE (s.sp.toNat - 80) 8 := by
      rw [hv2, hhi, hmodk]
    have hval : natVal s'.mem p xl.toNat = natVal s.mem xp.toNat xl.toNat - natVal s.mem yp.toNat yl.toNat := by
      rw [hsp, hlow, hv2', hsum, hsx]
    have hr0 : s'.regs 0 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [hc0, hhi, if_neg (by omega), if_neg (by omega)]; rfl
    refine tail impl R b L zp zc xp xl xc yp yl s p c L2 b2 s'.mem hM2 ((rd _ (by omega) (by omega)).trans hps)
      ((rd _ (by omega) (by omega)).trans hms) ((rd _ (by omega) (by omega)).trans hcs) hval _ rfl ?_ ?_ ?_ ?_ ?_ rfl
    all_goals janus_simp

end FvModexp.Arm64.NatSub
