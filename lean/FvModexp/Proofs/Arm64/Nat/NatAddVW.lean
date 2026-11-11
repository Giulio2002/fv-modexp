import FvModexp.Proofs.Arm64.Nat.NatAddTail
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.add` (arm64): after `addVV` (`+0xbc`): `if m > n { c = addVW(z[n:m], x[n:], c) }`, then the tail

At `+0xbc` the carry of `addVV` is in `80(RSP') = SP - 80`, `z[:n] = (X_lo + Y) mod B^n` and `x[n:m]` still holds `X_hi`.
`m = n`: straight to the tail (`+0x11c`). `m > n`: the slice expressions `z[n:m]`, `x[n:]` (masked pointers, caps
`c - n`, `xc - n`), the call (`addVW`, `stk 4144`, `above 40` at `SP' = SP - 160`), then the tail.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatAdd

-- (hAfterVV defined in NatAddTail)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem afterVV (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hVW : ∀ b L zp zl zc xp xl xc y, AddVWEns impl R b L zp zl zc xp xl xc y)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hxc : xl.toNat ≤ xc.toNat) (hxc63 : xc.toNat < 2 ^ 63)
    (hps : M.readLE (s.sp.toNat - 24) 8 = p) (hcs : M.readLE (s.sp.toNat - 64) 8 = c)
    (hlo : natVal M p yl.toNat + 2 ^ (64 * yl.toNat) * M.readLE (s.sp.toNat - 80) 8 =
      natVal s.mem xp.toNat yl.toNat + natVal s.mem yp.toNat yl.toNat)
    (hhi : natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
      natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hAfterVV)
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibNatAdd.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s' := by
  have hc2 : CodeIn ((Extracted.program.onlySegments [addVWfn]).link impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hVW' := fun b L => Ensures.toSummaryRegs7 (hVW b L) (noExit_restrict hap [addVWfn]) hc2
  clear hc2 hVW
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hyl := h.yl40
  have r1 := h.sxl; have r2 := h.syl; have r3 := h.sxc; have r4 := h.sxp
  have hsacc := h.sacc; have hal := h.al
  have hcw := Memory.readLE_lt M (s.sp.toNat - 80) 8
  by_cases hxy : yl.toNat = xl.toNat
  · -- `m = n`: no `addVW`
    janus_run [hm, r1, r2, hps, hcs] until [hTail]
    refine tail impl R b L zp zc xp xl xc yp yl s p c L' b' M h hyx hy0 hps hcs _ (by simpa using hcw) ?_ _ rfl
      ?_ ?_ rfl ?_ ?_ h18 rfl
    · rw [← hxy]; exact hlo
    all_goals janus_simp
  · have hlt : yl.toNat < xl.toNat := by omega
    have hm1 : ((yl - BitVec.ofNat 64 c).sshiftRight 63).toNat = 18446744073709551615 :=
      sshr63_of_lt _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
    have hm2 : ((yl - xc).sshiftRight 63).toNat = 18446744073709551615 := sshr63_of_lt _ _ (by omega) (by omega)
    have hand : yl.toNat &&& 18446744073709551615 = yl.toNat := and_ones64 _ yl.isLt
    have hs1 : (18446744073709551616 - yl.toNat + xl.toNat) % 18446744073709551616 = xl.toNat - yl.toNat :=
      sub_mod64 _ _ (by omega) xl.isLt
    have hs2 : (18446744073709551616 - yl.toNat + xc.toNat) % 18446744073709551616 = xc.toNat - yl.toNat :=
      sub_mod64 _ _ (by omega) xc.isLt
    have hs3 : (18446744073709551616 - yl.toNat + c) % 18446744073709551616 = c - yl.toNat :=
      sub_mod64 _ _ (by omega) (by omega)
    have hc64 : c % 18446744073709551616 = c := mod64_of_lt _ (by omega)
    have hmz : (p + 8 * yl.toNat) % 18446744073709551616 = p + 8 * yl.toNat := mod64_of_lt _ (by omega)
    have hmx : (xp.toNat + 8 * yl.toNat) % 18446744073709551616 = xp.toNat + 8 * yl.toNat :=
      mod64_of_lt _ (by have := h.x48; omega)
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
    have hzx3 : BitVec.ofNat 64 p + (yl &&& (yl - BitVec.ofNat 64 c).sshiftRight 63) <<< 3 =
          xp + (yl &&& (yl - xc).sshiftRight 63) <<< 3 ∨
        Apart (p + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) (xp.toNat + 8 * yl.toNat) (8 * (xl.toNat - yl.toNat)) := by
      rcases h.px with e | e
      · left; rw [e1, e2, show BitVec.ofNat 64 p = xp from BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_ofNat, e]; exact Nat.mod_eq_of_lt xp.isLt)]
      · right; unfold Apart at e ⊢; omega
    have hmv2 : ∀ j, 1 ≤ j → j ≤ xl.toNat - yl.toNat →
        R.ok (cA "runtime.memmove")
          [if j < c - yl.toNat then p + 8 * yl.toNat + 8 * j else p + 8 * yl.toNat,
            if j < xc.toNat - yl.toNat then xp.toNat + 8 * yl.toNat + 8 * j else xp.toNat + 8 * yl.toNat,
            8 * (xl.toNat - yl.toNat - j)] := fun j _ _ => h.mv _ _ _ (by omega)
    clear hzx2 hmv
    have hinv := h.inv; have hgrd := h.grd; have hgacc := h.gacc; have hg48 := h.g48; have hwrt := h.wrt
    have hgrt := h.grt; have hp8 := h.p8; have hx48 := h.x48
    sorry
    janus_run [hm, r1, r2, r3, r4, hps, hcs, hm1, hm2, hand, hs1, hs2, hs3, hc64, hmz, hmx, e1, e2] until [segAddr Extracted.program addVWfn]
    refine ReachesRet.call (hVW' b' L') rfl ⟨?_, ?_⟩ ?_
    · trace_state
      sorry
    · trace_state
      sorry
    · trace_state
      sorry

end FvModexp.Arm64.NatAdd
