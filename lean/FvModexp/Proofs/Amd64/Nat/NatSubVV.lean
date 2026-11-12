import FvModexp.Proofs.Amd64.Nat.NatSubCont
import FvModexp.Proofs.Amd64.Nat.SubVW
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.sub` (amd64): `c := subVV(z[0:n], x, y)` (`+0x13d` … `+0x189`), then `afterVV`

At `+0xe6`: `AX = p`, `CX = c`, `DI = xp`, `R8 = xc`, `R9 = yp`, `R10 = n`, `R11 = yc`.
`CMPQ R10, CX; JA panic; MOVQ CX, 0x50(SP); MOVQ AX, 0x78(SP)`, the ABI0 frame `0(SP) … 0x40(SP)`
(`RSP - 144 … RSP - 80`), `CALL addVV.abi0` (return address at `RSP - 152`, result word `0x48(SP) = RSP - 72`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.NatSub

theorem vv_after {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M1 w : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat)
    (hf1 : MemFrame M M1 [((s.regs 4).toNat - 152, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 48), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)])
    (hfr : MemFrame M1 w [(p, p + 8 * yl.toNat), ((s.regs 4).toNat - 152 + 80, (s.regs 4).toNat - 152 + 88)])
    (r24 : M1.readLE ((s.regs 4).toNat - 24) 8 = p) (r64 : M1.readLE ((s.regs 4).toNat - 64) 8 = xl.toNat) (r56 : M1.readLE ((s.regs 4).toNat - 56) 8 = c) :
    Mid R b L zp zc xp xl xc yp yl s p c L' b' w ∧ w.readLE ((s.regs 4).toNat - 24) 8 = p ∧
      w.readLE ((s.regs 4).toNat - 64) 8 = xl.toNat ∧ w.readLE ((s.regs 4).toNat - 56) 8 = c ∧
      natVal w (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
        natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) := by
  have hsp0 := h.sp0; have hpw := h.pw; have hxw := h.xw; have hcap := h.cap
  unfold Apart at hpw hxw
  have hws1 : WsOK s p xl.toNat [((s.regs 4).toNat - 152, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 48), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hws2 : WsOK s p xl.toNat [(p, p + 8 * yl.toNat), ((s.regs 4).toNat - 152 + 80, (s.regs 4).toNat - 152 + 88)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  refine ⟨(h.frame0 hws1 hf1).frame0 hws2 hfr, ?_, ?_, ?_, ?_⟩
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r24
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r64
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r56
  · rw [natVal_frame hfr, natVal_frame hf1]
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]
      refine ⟨?_, by omega⟩
      rcases h.px with e | e
      · omega
      · unfold Apart at e; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem vvH (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) (hA : AfterVVStmt impl hap R hmv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hxc : xl.toNat ≤ xc.toNat) (hxc63 : xc.toNat < 2 ^ 63)
    (hvx : natVal M xp.toNat yl.toNat = natVal s.mem xp.toNat yl.toNat)
    (hvh : natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
      natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat))
    (hvy : natVal M yp.toNat yl.toNat = natVal s.mem yp.toNat yl.toNat)
    (hge : natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h6 : S.regs 6 = xl) (h7 : S.regs 7 = xp) (h8 : S.regs 8 = xc) (h9 : S.regs 9 = yp)
    (h10 : S.regs 10 = yl) (h11 : S.regs 11 = yc)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostX 4288 R b L zp zc xp xl yp yl s s' := by
  have hc1 : CodeIn64 ((Extracted.program.onlySegments [subVVfn]).link impl) (LibNatSub.program.link impl) := by
    rw [LibNatSub.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hVV' := SubVVHyp.live (Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc1 (subVVHyp impl hap)) R b' L'
  clear hc1
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hyl := h.yl40
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hy48 := h.y48; have hwrt := h.wrt; have hgrt := h.grt
  have hpw := h.pw; have hpg := h.pg; have hxw := h.xw; have hyw := h.yw; have hgw := h.gw
  unfold Apart at hpw hpg hxw hyw hgw
  have hza : M.accessible p (8 * yl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * yl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxa : M.accessible xp.toNat (8 * yl.toNat) false = true :=
    Janus.Arm64.Memory.accessible_mono _ h.xacc (Nat.le_refl _) (by omega)
  have hya := h.yacc
  have hzx : p = xp.toNat ∨ Apart p (8 * yl.toNat) xp.toNat (8 * yl.toNat) := by
    rcases h.px with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hzy : p = yp.toNat ∨ Apart p (8 * yl.toNat) yp.toNat (8 * yl.toNat) := by
    rcases h.py with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hra := h.ra47
  have hpf := h.pf; have htw := h.tw
  unfold Apart at hpf htw
  janus64_run [hm, hfs, mod64_of_lt c (by omega), mod64_of_lt p (by omega), BitVec.msb_eq_decide] until [hAfterVV]
    calls [hVV']
  rename_i _ _ _ _ _ w _ _ hv hc hfr hinvw hg _
  obtain ⟨hm2, hps, hms, hcs, hhi⟩ := vv_after h hyx (M1 := _) (by janus_frame) hfr (by janus64_simp) (by janus64_simp)
    (by janus64_simp)
  have hlo : natVal w p yl.toNat + natVal s.mem yp.toNat yl.toNat =
      natVal s.mem xp.toNat yl.toNat + 2 ^ (64 * yl.toNat) * w.readLE ((s.regs 4).toNat - 72) 8 := by
    rw [show (s.regs 4).toNat - 72 = (s.regs 4).toNat - 152 + 80 by omega, ← hvx, ← hvy]
    exact hv
  have hb1 : w.readLE ((s.regs 4).toNat - 72) 8 ≤ 1 := by
    rw [show (s.regs 4).toNat - 72 = (s.regs 4).toNat - 152 + 80 by omega, hc]; split <;> omega
  refine hA b L zp zc xp xl xc yp yl s p c L' b' w hm2 hyx hy0 hxc hxc63 hps hcs hms hlo hb1 hge
    (hhi.trans hvh) _ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals janus64_simp

end FvModexp.Amd64.NatSub
