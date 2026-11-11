import FvModexp.Proofs.Arm64.Nat.MulAddWWCall

/-!
# `nat.mulAddWW` (arm64): the `mulAddVWW.abi0` call (`+0x7c` … `+0xa0`), then `tail`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.MulAddWW

/-- The facts after `mulAddVWW.abi0` returns, from the frames of the argument stores (`M → M1`) and of the call
(`M1 → w`). -/
theorem vww_after {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M1 w : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hf1 : MemFrame M M1 [(s.sp.toNat - 104, s.sp.toNat - 40), (s.sp.toNat - 32, s.sp.toNat - 24),
      (s.sp.toNat - 16, s.sp.toNat - 8)])
    (hfr : MemFrame M1 w [(p, p + 8 * xl.toNat), (s.sp.toNat - 112 + 72, s.sp.toNat - 112 + 80)])
    (r16 : M1.readLE (s.sp.toNat - 16) 8 = p) (r32 : M1.readLE (s.sp.toNat - 32) 8 = c) :
    Mid R b L zp zc xp xl s p c L' b' w ∧ w.readLE (s.sp.toNat - 16) 8 = p ∧
      w.readLE (s.sp.toNat - 32) 8 = c := by
  have hsp0 := h.sp0; have hpw := h.pw; have hcap := h.cap
  unfold Apart at hpw
  have hws1 : WsOK s p c [(s.sp.toNat - 104, s.sp.toNat - 40), (s.sp.toNat - 32, s.sp.toNat - 24),
      (s.sp.toNat - 16, s.sp.toNat - 8)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hws2 : WsOK s p c [(p, p + 8 * xl.toNat), (s.sp.toNat - 112 + 72, s.sp.toNat - 112 + 80)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  refine ⟨(h.frame0 hws1 hf1).frame0 hws2 hfr, ?_, ?_⟩
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r16
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact r32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem vww (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc y r : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hvx : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (xl.toNat + 1))
    (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = xp) (h4 : S.regs 4 = xl) (h5 : S.regs 5 = xc)
    (h6 : S.regs 6 = y) (h7 : S.regs 7 = r)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  have hV := vww_live impl hap R b' L'
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hwrt := h.wrt; have hgrt := h.grt
  have hpw := h.pw; have hpg := h.pg; have hgw := h.gw
  unfold Apart at hpw hpg hgw
  have hza : M.accessible p (8 * xl.toNat) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxa := h.xacc
  have hzx : p = xp.toNat ∨ Apart p (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    rcases h.px with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hc64 : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hp64 : p % 18446744073709551616 = p := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, hc64, hp64] until [hAfter] calls [hV]
  rename_i w hv hc hfr hinvw hg
  obtain ⟨hm2, hps, hcs⟩ := vww_after h (by janus_frame) hfr (by janus_simp) (by janus_simp)
  have hlo : natVal w p xl.toNat + 2 ^ (64 * xl.toNat) * w.readLE (s.sp.toNat - 40) 8 =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat := by
    have hxw := h.xw; unfold Apart at hxw
    rw [show s.sp.toNat - 40 = s.sp.toNat - 112 + 72 by omega, hc, hv, Nat.mod_add_div, ← hvx]
    congr 2
    exact natVal_frame (rs := [(s.sp.toNat - 104, s.sp.toNat - 40), (s.sp.toNat - 32, s.sp.toNat - 24),
      (s.sp.toNat - 16, s.sp.toNat - 8)]) (by janus_frame) (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact tail impl R b L zp zc xp xl y r s p c L' b' w hm2 hx0 hy0 hps hcs hlo _ rfl (by janus_simp) h28
    (by janus_simp) h18 rfl

end FvModexp.Arm64.MulAddWW
