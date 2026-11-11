import FvModexp.Proofs.Arm64.Nat.NatAddVW

/-!
# `nat.add` (arm64): `c := addVV(z[:n], x[:n], y[:n])` (`+0x94` … `+0xbc`), then `afterVV`

At `+0x94` (the join of the reuse and the `makeslice` paths of `z.make(m + 1)`): `R0 = p`, `R2 = c` (cap), `R3 = xp`,
`R5 = xc`, `R6 = yp`, `R7 = n`, `R8 = yc`. `CMP R2, R7; BHI panic; MOVD R2, 96(RSP); MOVD R0, 136(RSP)`, the ABI0
argument frame `8(RSP) … 72(RSP)` (`SP - 152 … SP - 80`), `CALL addVV.abi0` (result word `80(RSP) = SP - 80`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatAdd

/-- The facts after `addVV.abi0` returns, from the frames of the argument stores (`M → M1`) and of the call
(`M1 → w`). -/
theorem vv_after {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M1 w : Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat)
    (hf1 : MemFrame M M1 [(s.sp.toNat - 152, s.sp.toNat - 80), (s.sp.toNat - 64, s.sp.toNat - 56),
      (s.sp.toNat - 24, s.sp.toNat - 16)])
    (hfr : MemFrame M1 w [(p, p + 8 * yl.toNat), (s.sp.toNat - 160 + 80, s.sp.toNat - 160 + 88)])
    (r24 : M1.readLE (s.sp.toNat - 24) 8 = p) (r64 : M1.readLE (s.sp.toNat - 64) 8 = c) :
    Mid R b L zp zc xp xl xc yp yl s p c L' b' w ∧ w.readLE (s.sp.toNat - 24) 8 = p ∧
      w.readLE (s.sp.toNat - 64) 8 = c ∧
      natVal w (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
        natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) := by
  have hsp0 := h.sp0; have hpw := h.pw; have hxw := h.xw; have hcap := h.cap
  unfold Apart at hpw hxw
  have hws1 : WsOK s p c [(s.sp.toNat - 152, s.sp.toNat - 80), (s.sp.toNat - 64, s.sp.toNat - 56),
      (s.sp.toNat - 24, s.sp.toNat - 16)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hws2 : WsOK s p c [(p, p + 8 * yl.toNat), (s.sp.toNat - 160 + 80, s.sp.toNat - 160 + 88)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  refine ⟨(h.frame0 hws1 hf1).frame0 hws2 hfr, ?_, ?_, ?_⟩
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r24
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r64
  · rw [natVal_frame hfr, natVal_frame hf1]
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]
      refine ⟨?_, by omega⟩
      rcases h.px with e | e
      · omega
      · unfold Apart at e; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem vv (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hxc : xl.toNat ≤ xc.toNat) (hxc63 : xc.toNat < 2 ^ 63)
    (hvx : natVal M xp.toNat yl.toNat = natVal s.mem xp.toNat yl.toNat)
    (hvh : natVal M (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat) =
      natVal s.mem (xp.toNat + 8 * yl.toNat) (xl.toNat - yl.toNat))
    (hvy : natVal M yp.toNat yl.toNat = natVal s.mem yp.toNat yl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = xp) (h5 : S.regs 5 = xc) (h6 : S.regs 6 = yp)
    (h7 : S.regs 7 = yl) (h8 : S.regs 8 = yc)
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibNatAdd.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostR 4304 R b L zp zc xp xl yp yl s s' := by
  have hc1 : CodeIn ((Extracted.program.onlySegments [addVVfn]).link impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hVV' : Summary (LibNatAdd.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b' L')
      (fun s s' => GoABI0.Ret0 s s' (VVLQ R b' L' s)) :=
    AddVVHyp.live (Janus.Contracts.EqHashModel.Summary.of_codeIn hc1 (addVVHyp impl hap)) R b' L'
  clear hc1
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hyl := h.yl40
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hy48 := h.y48; have hwrt := h.wrt; have hgrt := h.grt
  have hpw := h.pw; have hpg := h.pg; have hxw := h.xw; have hyw := h.yw; have hgw := h.gw
  unfold Apart at hpw hpg hxw hyw hgw
  have hza : M.accessible p (8 * yl.toNat) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * yl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxa : M.accessible xp.toNat (8 * yl.toNat) false = true := Memory.accessible_mono _ h.xacc (Nat.le_refl _) (by omega)
  have hya := h.yacc
  have hzx : p = xp.toNat ∨ Apart p (8 * yl.toNat) xp.toNat (8 * yl.toNat) := by
    rcases h.px with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hzy : p = yp.toNat ∨ Apart p (8 * yl.toNat) yp.toNat (8 * yl.toNat) := by
    rcases h.py with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hc64 : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hp64 : p % 18446744073709551616 = p := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, hc64, hp64] until [hAfterVV] calls [hVV']
  rename_i w hv hc hfr hinvw hg
  obtain ⟨hm2, hps, hcs, hhi⟩ := vv_after h hyx (by janus_frame) hfr (by janus_simp) (by janus_simp)
  have hlo : natVal w p yl.toNat + 2 ^ (64 * yl.toNat) * w.readLE (s.sp.toNat - 80) 8 =
      natVal s.mem xp.toNat yl.toNat + natVal s.mem yp.toNat yl.toNat := by
    rw [hv, show s.sp.toNat - 80 = s.sp.toNat - 160 + 80 by omega, hc, Nat.mod_add_div, ← hvx, ← hvy]
  exact afterVV impl hap R hmv b L zp zc xp xl xc yp yl s p c L' b' w hm2 hyx hy0 hxc hxc63 hps hcs hlo
    (hhi.trans hvh) _ rfl (by janus_simp) h28 (by janus_simp) h18 rfl

end FvModexp.Arm64.NatAdd
