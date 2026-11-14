import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W4Seg
import FvModexp.Proofs.Amd64.Exp.W4ZcP

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcT (impl : List Amd64.Segment) {R : RtInv}
    (hmv : MemmoveLive64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {ret : W64} {Q : State → Prop}
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi k pd V : Nat) (M : Memory)
    (r5 : W64)
    (he : Env R L g fs sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g fs sp n M zp zc) (hk : k ≤ 15)
    (hzzc : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi64 : yi < 2 ^ 64)
    (hpd : Inp R L sp n M pd) (hzd : Apart zp (8 * zc) pd (8 * n)) (hvd : M.readLE pd (8 * n) = V)
    (r168 : M.readLE (sp + 0x168) 8 = zp) (r88 : M.readLE (sp + 0x88) 8 = zc)
    (r398 : M.readLE (sp + 0x398) 8 = ylen) (r390 : M.readLE (sp + 0x390) 8 = yp)
    (r3a8 : M.readLE (sp + 0x3a8) 8 = mp) (rd8 : M.readLE (sp + 0xd8) 8 = k0) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (r3b8 : M.readLE (sp + 0x3b8) 8 = mc)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, pd, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6208696) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 (k * 4))
    (h8 : S.regs 8 = BitVec.ofNat 64 zzp) (h9 : S.regs 9 = BitVec.ofNat 64 yi) (h10 : S.regs 10 = BitVec.ofNat 64 pd)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc)
    (h15 : S.regs 15 = BitVec.ofNat 64 (k + 1))
    (KT : ∀ S' : State, S'.rip = BitVec.ofNat 64 testL → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 2 = BitVec.ofNat 64 zc → S'.regs 8 = BitVec.ofNat 64 zzp →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 12 = BitVec.ofNat 64 zzc → S'.regs 3 = BitVec.ofNat 64 mp →
      S'.regs 6 = BitVec.ofNat 64 k0 → S'.regs 10 = BitVec.ofNat 64 mc →
      S'.regs 9 = BitVec.ofNat 64 ((yi * 2 ^ (64 - k * 4)) % 2 ^ 64) → S'.regs 15 = BitVec.ofNat 64 k - 1#64 →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 13 = BitVec.ofNat 64 ylen → S'.regs 1 = BitVec.ofNat 64 (ylen - 1) →
      MemFrame M S'.mem (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M S'.mem L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions → S'.mem.readLE zp (8 * n) = V →
      S'.mem.readLE (sp + 0x140) 8 = n → S'.mem.readLE (sp + 0xe8) 8 = ylen - 1 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hz0 := hz
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hz0
  unfold Apart at hzd z6
  have hpa := hpd.1
  have hza : M.accessible zp (8 * n) true = true := Arm64.Memory.accessible_mono _ z3 (Nat.le_refl _) (by omega)
  have hpb := hpd.2.2.2
  unfold Apart at hpb
  have e8 : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
      ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hz8n : InRanges zp (8 * n) L ∨ Outside zp (8 * n) R.rt :=
    z5.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  janus64_run [e8] until [6208751] calls [hmv L b]
  rename_i _ _ _ _ m1 _ _ hF1 hL1 hI1 hC1
  obtain ⟨⟨q168, q138, q88, q390, q370, q118, q120, q398, q140, q3a8, qd8, q3b0, q3b8⟩, qF, qL, qv⟩ :=
    zcPost (mp := mp) (mc := mc) (k0 := k0) (yp := yp) (ylen := ylen) he hz hk hzzc hzzp hyi64 hpb hvd
      r168 r88 r398 r390 r3a8 rd8 r3b0 r3b8 hF1 hL1 hC1
  clear hF1 hL1 hC1
  have e64 := en k hk
  have hm64 : (BitVec.ofNat 64 (64 - k * 4)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have fin : ∀ (Mf : Memory), Mf = (m1.writeLE (sp + 320) 8 n).writeLE (sp + 232) 8 (ylen - 1) →
      MemFrame M Mf (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) ∧ LiveFrame M Mf L [(zp, zp + 8 * n)] ∧
      R.inv b L g (view R.rt L Mf) ∧ Mf.regions = M.regions ∧ Mf.readLE zp (8 * n) = V ∧
      Mf.readLE (sp + 0x140) 8 = n ∧ Mf.readLE (sp + 0xe8) 8 = ylen - 1 := by
    intro Mf e; subst e
    refine ⟨(qF.writeLE_inRanges _ ?_).writeLE_inRanges _ ?_, (qL.writeLE _ ?_).writeLE _ ?_,
      FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega)))
        (FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) hI1), ?_, ?_, ?_, ?_⟩
    · exact ⟨(sp + 0x138, sp + 0x148), by simp [cw], by simp only; omega, by simp only; omega⟩
    · exact ⟨(sp + 0xe8, sp + 0xf0), by simp [cw], by simp only; omega, by simp only; omega⟩
    · exact FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)
    · exact FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)
    · rw [Arm64.Memory.regions_writeLE, Arm64.Memory.regions_writeLE]; exact hrg1
    · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact qv
    · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]
      omega
    · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]
      omega
  have e1 := eyl ylen hyl hyl'
  by_cases hk0 : k = 0
  · subst hk0
    refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 testL) ?_
    janus64_run [q168, q138, q88, q390, q370, q118, q120, q398, q140, q3a8, qd8, q3b0, q3b8, e64, hm64] until [testL]
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := fin _ rfl
    refine KT _ rfl ?_ ?_ ?_ hfs ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ f1 f2 f3 f4 f5 f6 f7
    all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
    all_goals first | exact h5 | exact h14 | exact e1 | exact ey0 yi | exact BitVec.sub_add_cancel _ _ | rfl
  · refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 testL) ?_
    janus64_run [q168, q138, q88, q390, q370, q118, q120, q398, q140, q3a8, qd8, q3b0, q3b8, e64, hm64] until [testL]
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := fin _ rfl
    refine KT _ rfl ?_ ?_ ?_ hfs ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ f1 f2 f3 f4 f5 f6 f7
    all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
    all_goals first | exact h5 | exact h14 | exact e1 | exact ek21 k hk | exact BitVec.sub_add_cancel _ _ | rfl | skip
    rw [if_pos (show 64 - k * 4 < 64 by omega), and1, show (18446744073709551616 - k * 4) % 64 = 64 - k * 4 by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_mul_mod, Nat.mod_mod]

end FvModexp.Amd64.W4Pro
