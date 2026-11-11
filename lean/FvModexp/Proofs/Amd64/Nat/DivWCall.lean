import FvModexp.Proofs.Amd64.Nat.DivWNorm

/-!
# `nat.divW` (amd64): `r = divWVW(z, 0, x, y); q = z.norm()` (`+0xfb` … return)

At `+0xfb` (the join of the reuse and `makeslice` paths of `z.make(m)`): `AX = p`, `CX = c`, `SI = DX = m`,
`DI = xp`, `R8 = xc`, `R9 = y`. Stores `0x48(RSP') = c`, `0x40(RSP') = m`, `0x68(RSP') = p` (`RSP - 56, -64, -24`),
argument shuffle, `CALL divWVW` (`+0x120`, returns to `+0x125`); then `DX = p`, `BX = m`, `JMP norm`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

abbrev hMid : Nat := segAddr Extracted.program fn + 0xfb
abbrev hAfter : Nat := segAddr Extracted.program fn + 0x125

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hps : M.readLE ((s.regs 4).toNat - 24) 8 = p) (hms : M.readLE ((s.regs 4).toNat - 64) 8 = xl.toNat)
    (hcs : M.readLE ((s.regs 4).toNat - 56) 8 = c)
    (hv : natVal M p xl.toNat = natVal s.mem xp.toNat xl.toNat / y.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hAfter)
    (h0 : (S.regs 0).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat)
    (hsp : S.regs 4 = s.regs 4 - 128#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  janus64_run [hm, hps, hms, BitVec.msb_eq_decide] until [hNorm]
  refine norm impl s M p c xl.toNat _ (S.regs 0) _ (fun s' n' hm' h0' h1' h2' h3' hfs' hn' hv' hnm' =>
      h.post s' n' hm' h0' h1' h2' (by rw [h3']; exact h0) hfs' hn' hv' hnm') hcap (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)))
    h.lr h.fp hcs hal hsp0 hsp1 hsacc h.ra47 xl.toNat _ (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ h14 ?_ ?_ ?_ ?_ rfl hv
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hx15 | exact hdf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem call (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc y : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hy0 : y.toNat ≠ 0)
    (hvx : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h6 : S.regs 6 = xl) (h2 : S.regs 2 = xl) (h7 : S.regs 7 = xp)
    (h8 : S.regs 8 = xc) (h9 : S.regs 9 = y)
    (hsp : S.regs 4 = s.regs 4 - 128#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y s s' := by
  have hV := dvw impl hap R b' L'
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hx0 := h.x0
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hwrt := h.wrt; have hgrt := h.grt; have hgok := h.gok; have hgrd := h.grd; have hgacc := h.gacc
  have hg48 := h.g48; have hra := h.ra47; have htls := h.tls; have htacc := h.tacc; have htrt := h.trt
  have htb := h.tlsg.base
  have hpw := h.pw; have hpg := h.pg; have hgw := h.gw; have hxw := h.xw; have hpf := h.pf; have htw := h.tw
  unfold Apart at hpw hpg hgw hxw hpf htw
  have hza : M.accessible p (8 * xl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxh := h.xheld
  have hxa := h.xacc
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hzx : BitVec.ofNat 64 p = xp ∨ Apart p (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    rcases h.px with e | e
    · left; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt xp.isLt]
    · right; unfold Apart at e ⊢; omega
  have hx15s := h.x15
  janus64_run [hm, hfs, hx15, mod64_of_lt (a := c) (by omega), mod64_of_lt (a := p) (by omega), BitVec.msb_eq_decide]
    until [hAfter] calls [hV]
  rename_i hfs2 hdf2 L2 b2 hext hbb hr0 hv hinv2 hF hLF
  have e136 : (s.regs 4 - 136#64).toNat = (s.regs 4).toNat - 136 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hW : MemFrame M ((((M.writeLE ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 64) 8 xl.toNat).writeLE
      ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 136) 8 6219237)
      [((s.regs 4).toNat - 136, (s.regs 4).toNat - 128), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 48),
        ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] := by
    janus_frame
  have hws1 : WsOK s p c [((s.regs 4).toNat - 136, (s.regs 4).toNat - 128),
      ((s.regs 4).toNat - 64, (s.regs 4).toNat - 48), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hm1 := h.frame0 hws1 hW
  have hF' : MemFrame ((((M.writeLE ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 64) 8
      xl.toNat).writeLE ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 136) 8 6219237) s'.mem
      (R.rt ++ [((s.regs 4).toNat - 200, (s.regs 4).toNat - 64), (p, p + 8 * xl.toNat)]) := by
    refine hF.mono fun a n ho => ?_
    simp only [win, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e136, outside_append, outside_cons, outside_nil,
      and_true] at ho ⊢
    obtain ⟨hr, c1, c3⟩ := ho
    exact ⟨⟨hr, by omega⟩, c3⟩
  have hws2 : WsOK s p c [((s.regs 4).toNat - 200, (s.regs 4).toNat - 64), (p, p + 8 * xl.toNat)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  have hM2 := hm1.frame hws2 hF' (LiveFrame.mono_ws hLF fun a n ho => by
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; exact ho.2) hext hbb hinv2
  have rd : ∀ a, (s.regs 4).toNat - 64 ≤ a → a + 8 ≤ (s.regs 4).toNat - 8 → s'.mem.readLE a 8 =
      ((((M.writeLE ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 64) 8 xl.toNat).writeLE
        ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 136) 8 6219237).readLE a 8 := by
    intro a h1 h2
    refine hF'.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩
  have hx1 : natVal ((((M.writeLE ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 64) 8 xl.toNat).writeLE
      ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 136) 8 6219237) xp.toNat xl.toNat =
      natVal s.mem xp.toNat xl.toNat := by
    rw [← hvx]; exact natVal_frame hW (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdv : DivWVW.Dvd ((((M.writeLE ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 64) 8
      xl.toNat).writeLE ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 136) 8 6219237) xl 0#64 xp =
      natVal s.mem xp.toNat xl.toNat := by
    unfold DivWVW.Dvd; rw [hx1]; simp
  rw [hdv] at hr0 hv
  refine tail impl R b L zp zc xp xl y s p c L2 b2 s'.mem hM2 ?_ ?_ ?_ hv _ ?_ hr0 ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · rw [rd _ (by omega) (by omega)]; janus64_simp
  · rw [rd _ (by omega) (by omega)]; janus64_simp
  · rw [rd _ (by omega) (by omega)]; janus64_simp
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hx15 | (rw [hfs2]) | (rw [hfs2]; exact hfs) | (rw [hdf2]; exact hdf) | exact hdf

end FvModexp.Amd64.DivW
