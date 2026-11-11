import FvModexp.Proofs.Amd64.Nat.MulAddWWCall

/-!
# `nat.mulAddWW` (amd64): the `mulAddVWW.abi0` call (`+0xae` … `+0xed`), then `tail`

At `+0xae`: `AX = p`, `BX = m + 1`, `CX = c`, `DI = xp`, `SI = m`, `R8 = xc`, `R9 = y`, `R10 = r`.
`CMPQ SI, CX; JA panic; MOVQ CX, 0x48(SP); MOVQ AX, 0x58(SP)`, the ABI0 frame `0(SP) … 0x38(SP)`
(`RSP - 104 … RSP - 40`), `CALL mulAddVWW.abi0` (return address at `RSP - 112`, result `0x40(SP) = RSP - 40`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.MulAddWW

theorem vww_after {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M1 w : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hf1 : MemFrame M M1 [((s.regs 4).toNat - 112, (s.regs 4).toNat - 40), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24),
      ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)])
    (hfr : MemFrame M1 w [(p, p + 8 * xl.toNat), ((s.regs 4).toNat - 112 + 72, (s.regs 4).toNat - 112 + 80)])
    (r16 : M1.readLE ((s.regs 4).toNat - 16) 8 = p) (r32 : M1.readLE ((s.regs 4).toNat - 32) 8 = c) :
    Mid R b L zp zc xp xl s p c L' b' w ∧ w.readLE ((s.regs 4).toNat - 16) 8 = p ∧
      w.readLE ((s.regs 4).toNat - 32) 8 = c := by
  have hsp0 := h.sp0; have hpw := h.pw; have hcap := h.cap
  unfold Apart at hpw
  have hws1 : WsOK s p c [((s.regs 4).toNat - 112, (s.regs 4).toNat - 40), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24),
      ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hws2 : WsOK s p c [(p, p + 8 * xl.toNat), ((s.regs 4).toNat - 112 + 72, (s.regs 4).toNat - 112 + 80)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  refine ⟨(h.frame0 hws1 hf1).frame0 hws2 hfr, ?_, ?_⟩
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r16
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc y r : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hvx : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h3 : S.regs 3 = BitVec.ofNat 64 (xl.toNat + 1))
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h7 : S.regs 7 = xp) (h6 : S.regs 6 = xl) (h8 : S.regs 8 = xc)
    (h9 : S.regs 9 = y) (h10 : S.regs 10 = r)
    (hsp : S.regs 4 = s.regs 4 - 104#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ Post R b L zp zc xp xl y r s s' := by
  have hV := vww_live impl hap R b' L'
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hwrt := h.wrt; have hgrt := h.grt
  have hpw := h.pw; have hpg := h.pg; have hgw := h.gw
  unfold Apart at hpw hpg hgw
  have hza : M.accessible p (8 * xl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxa := h.xacc
  have hzx : p = xp.toNat ∨ Apart p (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    rcases h.px with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hra := h.ra47
  have hpf := h.pf; have htw := h.tw
  unfold Apart at hpf htw
  janus64_run [hm, hfs, mod64_of_lt (a := c) (by omega), mod64_of_lt (a := p) (by omega), BitVec.msb_eq_decide] until [hAfter]
    calls [hV]
  rename_i _ _ _ _ _ w _ _ hv hc hfr hinvw hg _
  obtain ⟨hm2, hps, hcs⟩ := vww_after h (M1 := _) (by janus_frame) hfr (by janus64_simp) (by janus64_simp)
  have hlo : natVal w p xl.toNat + 2 ^ (64 * xl.toNat) * w.readLE ((s.regs 4).toNat - 40) 8 =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat := by
    have hxw := h.xw; unfold Apart at hxw
    rw [show (s.regs 4).toNat - 40 = (s.regs 4).toNat - 112 + 72 by omega, hc, hv, Nat.mod_add_div, ← hvx]
    congr 2
    exact natVal_frame (rs := [((s.regs 4).toNat - 112, (s.regs 4).toNat - 40),
      ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)]) (by janus_frame)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine tail impl R b L zp zc xp xl y r s p c L' b' w hm2 hx0 hy0 hps hcs hlo _ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus64_simp

end FvModexp.Amd64.MulAddWW
