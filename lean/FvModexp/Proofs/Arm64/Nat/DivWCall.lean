import FvModexp.Proofs.Arm64.Nat.DivWNorm

/-!
# `nat.divW` (arm64): `r = divWVW(z, 0, x, y); q = z.norm()` (`+0xbc` … return)

At `+0xbc` (the join of the reuse and `makeslice` paths of `z.make(m)`): `R0 = p`, `R1 = m`, `R2 = c`, `R3 = xp`,
`R4 = m`, `R5 = xc`, `R6 = y`. Stores `88(RSP') = c`, `80(RSP') = m`, `120(RSP') = p` (`SP - 56`, `SP - 64`, `SP - 24`),
argument shuffle, `CALL divWVW` (`+0xe0`, returns to `+0xe4`); then `R8 = p`, `R1 = m`, `JMP norm`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivW

/-- The join after `z.make(m)` on the `divWVW` path. -/
abbrev hMid : Nat := segAddr Extracted.program fn + 0xbc
/-- The return site of `divWVW`. -/
abbrev hAfter : Nat := segAddr Extracted.program fn + 0xe4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hps : M.readLE (s.sp.toNat - 24) 8 = p) (hms : M.readLE (s.sp.toNat - 64) 8 = xl.toNat)
    (hcs : M.readLE (s.sp.toNat - 56) 8 = c)
    (hv : natVal M p xl.toNat = natVal s.mem xp.toNat xl.toNat / y.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hAfter)
    (h0 : (S.regs 0).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat)
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  janus_run [hm, hps, hms] until [hNorm]
  refine norm impl s M p c xl.toNat _ (S.regs 0) _ (fun s' n' hm' h0' h1' h2' h3' hn' hv' hnm' =>
      h.post s' n' hm' h0' h1' h2' (by rw [h3']; exact h0) hn' hv' hnm') hcap (by omega) (by omega)
    (Memory.accessible_weaken _ (Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)))
    h.lr h.fp hcs hal hsp0 hsp1 hsacc h.lr4 h.lr48 xl.toNat _ (Nat.le_refl _) rfl ?_ ?_ ?_ ?_ h28 ?_ h18 rfl hv
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem call (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc y : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hy0 : y.toNat ≠ 0)
    (hvx : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = xl) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = xp) (h4 : S.regs 4 = xl)
    (h5 : S.regs 5 = xc) (h6 : S.regs 6 = y)
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s' := by
  have hV := dvw impl hap R b' L'
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hx0 := h.x0
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hwrt := h.wrt; have hgrt := h.grt; have hgok := h.gok; have hgrd := h.grd; have hgacc := h.gacc
  have hg48 := h.g48
  have hpw := h.pw; have hpg := h.pg; have hgw := h.gw; have hxw := h.xw
  unfold Apart at hpw hpg hgw hxw
  have hza : M.accessible p (8 * xl.toNat) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxh := h.xheld
  have hxa := h.xacc
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hzx : BitVec.ofNat 64 p = xp ∨ Apart p (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    rcases h.px with e | e
    · left; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt xp.isLt]
    · right; unfold Apart at e ⊢; omega
  have hc64 : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hp64 : p % 18446744073709551616 = p := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, hc64, hp64] until [hAfter] calls [hV]
  rename_i L2 b2 hext hbb hr0 hv hinv2 hF hLF
  have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hW : MemFrame M (((M.writeLE (s.sp.toNat - 56) 8 c).writeLE (s.sp.toNat - 64) 8 xl.toNat).writeLE
      (s.sp.toNat - 24) 8 p) [(s.sp.toNat - 64, s.sp.toNat - 48), (s.sp.toNat - 24, s.sp.toNat - 16)] := by
    janus_frame
  have hws1 : WsOK s p c [(s.sp.toNat - 64, s.sp.toNat - 48), (s.sp.toNat - 24, s.sp.toNat - 16)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  have hm1 := h.frame0 hws1 hW
  have hF' : MemFrame (((M.writeLE (s.sp.toNat - 56) 8 c).writeLE (s.sp.toNat - 64) 8 xl.toNat).writeLE
      (s.sp.toNat - 24) 8 p) s'.mem (R.rt ++ [(s.sp.toNat - 296, s.sp.toNat - 152), (s.sp.toNat - 136, s.sp.toNat - 72),
        (p, p + 8 * xl.toNat)]) := by
    refine hF.mono fun a n ho => ?_
    simp only [winA, e144, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, c1, c2, c3⟩ := ho
    exact ⟨⟨hr, by omega, by omega⟩, c3⟩
  have hws2 : WsOK s p c [(s.sp.toNat - 296, s.sp.toNat - 152), (s.sp.toNat - 136, s.sp.toNat - 72),
      (p, p + 8 * xl.toNat)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hM2 := hm1.frame hws2 hF' (LiveFrame.mono_ws hLF fun a n ho => by
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.2.2) hext hbb hinv2
  have rd : ∀ a, s.sp.toNat - 72 ≤ a → a + 8 ≤ s.sp.toNat - 8 → s'.mem.readLE a 8 =
      (((M.writeLE (s.sp.toNat - 56) 8 c).writeLE (s.sp.toNat - 64) 8 xl.toNat).writeLE
        (s.sp.toNat - 24) 8 p).readLE a 8 := by
    intro a h1 h2
    refine hF'.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
  have hx1 : natVal (((M.writeLE (s.sp.toNat - 56) 8 c).writeLE (s.sp.toNat - 64) 8 xl.toNat).writeLE
      (s.sp.toNat - 24) 8 p) xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat := by
    rw [← hvx]; exact natVal_frame hW (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdv : DivWVW.Dvd (((M.writeLE (s.sp.toNat - 56) 8 c).writeLE (s.sp.toNat - 64) 8 xl.toNat).writeLE
      (s.sp.toNat - 24) 8 p) xl 0#64 xp = natVal s.mem xp.toNat xl.toNat := by
    unfold DivWVW.Dvd; rw [hx1]; simp
  rw [hdv] at hr0 hv
  refine tail impl R b L zp zc xp xl y s p c L2 b2 s'.mem hM2 ?_ ?_ ?_ hv _ ?_ hr0 ?_ ?_ ?_ ?_ rfl
  · rw [rd _ (by omega) (by omega)]; janus_simp
  · rw [rd _ (by omega) (by omega)]; janus_simp
  · rw [rd _ (by omega) (by omega)]; janus_simp
  all_goals janus_simp

end FvModexp.Arm64.DivW
