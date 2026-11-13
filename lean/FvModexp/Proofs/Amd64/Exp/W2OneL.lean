import FvModexp.Proofs.Amd64.Exp.W2One

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `one := make(nat, n)` for `n > 4` (`makeslice(Word, n, n)`, call fn+0x7c0), `one[0] = 1`,
`powers` zeroing, call setup of `stk.nat(5n)` (agent expmc s61) — twin of `oneSmall` / arm64 `W2Pro.oneLarge`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

theorem apartAll_out {a k : Nat} {L : List (Nat × Nat)} (h : ApartAll a k L) (j : Nat) (hj : j ≤ k) :
    Outside a j L :=
  Janus.Contracts.outside_of_forall (fun r hr => by have := h r hr; unfold Apart at this; omega)

/-- a write into `ow` or into `[p, p + 8)` keeps the frame `ow sp ++ [(p, p + 8)]` -/
theorem owp_mf {sp p : Nat} {M M' : Memory} (h : MemFrame M M' (ow sp ++ [(p, p + 8)])) {a k : Nat} (v : Nat)
    (hw : (sp - 4296 ≤ a ∧ a + k ≤ sp + 0x18) ∨ (sp + 0xa0 ≤ a ∧ a + k ≤ sp + 0xa8) ∨
      (sp + 0xf8 ≤ a ∧ a + k ≤ sp + 0x108) ∨ (sp + 0x150 ≤ a ∧ a + k ≤ sp + 0x170) ∨
      (sp + 0x190 ≤ a ∧ a + k ≤ sp + 0x198) ∨ (sp + 0x1b0 ≤ a ∧ a + k ≤ sp + 0x218) ∨
      (sp + 0x220 ≤ a ∧ a + k ≤ sp + 0x228) ∨ (p ≤ a ∧ a + k ≤ p + 8)) :
    MemFrame M (M'.writeLE a k v) (ow sp ++ [(p, p + 8)]) := by
  refine h.writeLE_inRanges v ?_
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(sp - 4296, sp + 0x18), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0xa0, sp + 0xa8), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0xf8, sp + 0x108), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x150, sp + 0x170), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x190, sp + 0x198), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x1b0, sp + 0x218), by simp [ow], h1, h2⟩
  · exact ⟨(sp + 0x220, sp + 0x228), by simp [ow], h1, h2⟩
  · exact ⟨(p, p + 8), by simp, h1, h2⟩

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem oneLarge (impl : List Amd64.Segment) {R : RtInv}
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {ret : W64} {Q : State → Prop}
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n st rrp rrl rrc zzp zzc : Nat} {M : Memory} {r5 : W64}
    (he : Env R L g fs sp M) (hn4 : 4 < n) (hn16 : n ≤ 2 ^ 16) (hd : Extracted.program.DataLoaded M)
    (hrr : rrp < 2 ^ 64) (hrl : rrl < 2 ^ 64) (hrc : rrc < 2 ^ 64) (hzp : zzp < 2 ^ 64) (hzc : zzc < 2 ^ 64)
    (s3b0 : M.readLE (sp + 0x298) 8 = n) (s148 : M.readLE (sp + 0x148) 8 = 5 * n) (s3d8 : M.readLE (sp + 0x2c0) 8 = st)
    (hacc3 : M.accessible (sp + 0x2c0) 8 false = true) (hca : Outside (sp + 0x2a8) 0x20 R.rt)
    (hok : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, n, n] ∧ blockSize (8 * n) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 rrJ) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 rrp) (h1 : S.regs 1 = BitVec.ofNat 64 rrl)
    (h8 : S.regs 8 = BitVec.ofNat 64 rrc) (h2 : S.regs 2 = BitVec.ofNat 64 zzc) (h6 : S.regs 6 = BitVec.ofNat 64 zzp)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KA : ∀ (S' : State) (onep : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.rip = BitVec.ofNat 64 snE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) → S'.regs 0 = BitVec.ofNat 64 st →
      S'.regs 3 = BitVec.ofNat 64 (5 * n) → S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      OnePost R L L' b b' g fs sp n M S'.mem onep → OneSl sp rrp rrl rrc zzp zzc S'.mem →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  obtain ⟨hok1, hbs⟩ := hok
  have hwt : Apart wT 16 (sp - 4296) (4296 + 0x2a8) := apart_of_data hd 1 (by decide) (by decide) hwacc
  janus_eval_nat h_t : wT
  rw [h_t] at hok1 hwt
  unfold Apart at hwt
  obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
  have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
      ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hgt : ¬ n ≤ 4 := by omega
  janus64_run [s3b0, s148, s3d8, hws, hwp, BitVec.msb_eq_decide] until [6186112] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ hz hsz _ hinv' _ _ _
  have hpw := out_inR hwrt hIn
  have hpg := out_inR hgrt hIn
  have hpf := out_inR hfrt hIn
  have hpca := out_inR hca hIn
  have hp8 : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
  have hwF : MemFrame M ((((((M.writeLE (sp + 160) 8 zzc).writeLE (sp + 400) 8 zzp).writeLE (sp + 256) 8 rrc).writeLE (sp + 248) 8 rrl).writeLE
      (sp + 544) 8 rrp).writeLE (sp - 8) 8 6212549) (ow sp) := by
    repeat (refine ow_mf ?_ _ (by omega))
    exact MemFrame.refl _ _
  have hwL : LiveFrame M ((((((M.writeLE (sp + 160) 8 zzc).writeLE (sp + 400) 8 zzp).writeLE (sp + 256) 8 rrc).writeLE (sp + 248) 8 rrl).writeLE
      (sp + 544) 8 rrp).writeLE (sp - 8) 8 6212549) L [] := by
    repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  have hmF : MemFrame M m (R.rt ++ ow sp) := by
    refine (hwF.widen R.rt).trans hMF (fun a k h => ⟨h, ?_⟩)
    simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1, by omega, by omega⟩
  have r984 : m.readLE (sp + 704) 8 = st := by
    rw [hMF.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hca.of_sub (by omega) (by omega), by omega, by omega⟩)]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    exact s3d8
  have hX : LiveExt R L (L ++ [(ptr.toNat, ptr.toNat + blockSize (8 * n) true)]) :=
    LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hinL : InRanges ptr.toNat 8 (L ++ [(ptr.toNat, ptr.toNat + blockSize (8 * n) true)]) :=
    ⟨(ptr.toNat, ptr.toNat + blockSize (8 * n) true), by simp, Nat.le_refl _, by simp only; omega⟩
  refine KA _ ptr.toNat _ (b - blockSize (8 * n) true) rfl ?_ ?_ ?_ ?_ ?_ hfs ?_ rfl ⟨?env, hX, by
    simp only [show 4 < n from hn4, ite_true]; omega, ?mf, ?lf, ?inv, ?rg, ?r328, ?one,
    Or.inr ⟨⟨(ptr.toNat, ptr.toNat + blockSize (8 * n) true), by simp, Nat.le_refl _, by simp only; omega⟩,
      hIn.sub (Nat.le_refl _) (by omega), fun r hr => by have := hAp r hr; unfold Apart at this ⊢; omega, ?acc,
      by omega, hp8⟩⟩ ?sl
  case mf =>
    refine hmF.trans (rs' := ow sp ++ [(ptr.toNat, ptr.toNat + 8)]) ?_ (fun a k h => ⟨h, by
      have := out_inR (by simp only [outside_append] at h; exact h.1) hIn
      simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨h.2, by omega⟩⟩)
    repeat (refine owp_mf ?_ _ (by omega))
    exact MemFrame.refl _ _
  case env =>
    refine Env.frame he ?_ (out_of_in hgw (ow sp) (ow_in sp)) (out_of_in hfw (ow sp) (ow_in sp)) hX
    refine hmF.trans (rs' := ow sp ++ [(ptr.toNat, ptr.toNat + 8)]) ?_ (fun a k h => ⟨h, by
      have := out_inR (by simp only [outside_append] at h; exact h.1) hIn
      simp only [ow, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨h.2, by omega⟩⟩)
    repeat (refine owp_mf ?_ _ (by omega))
    exact MemFrame.refl _ _
  case acc =>
    simp only [Arm64.Memory.accessible_writeLE]
    rw [hMF.accessible]
    simp only [Arm64.Memory.accessible_writeLE]
    exact Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  case inv =>
    refine FvModexp.Expmc.inv_frame (m := m) (ws := ow sp ++ [(ptr.toNat, ptr.toNat + 8)]) ?_ (fun r hr => ?_) hinv'
    · repeat (refine owp_mf ?_ _ (by omega))
      exact MemFrame.refl _ _
    rcases List.mem_append.1 hr with hr | hr
    · exact ow_out hwrt r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact Or.inl (by simpa using hinL)
  case lf =>
    refine LiveFrame.trans (m' := m) (hwL.trans hLF (fun _ _ h => h)) ?_ (fun _ _ h => h)
    repeat (refine LiveFrame.writeLE ?_ _ (by
      first
        | exact FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)
        | exact apartAll_out hAp 8 (by omega)))
    exact LiveFrame.refl _ _ _
  case rg => simp only [Arm64.Memory.regions_writeLE]; exact hrg1
  case r328 =>
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      Nat.reducePow]
    omega
  case one =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [rd8, Arm64.Memory.readLE_writeLE_self, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hz.readLE (k := 8) (j := 8 * k) (by omega)]
  case sl =>
    have rm : ∀ K, (K = 544 ∨ K = 256 ∨ K = 248 ∨ K = 160 ∨ K = 400) →
        m.readLE (sp + K) 8 = ((((((M.writeLE (sp + 160) 8 zzc).writeLE (sp + 400) 8 zzp).writeLE (sp + 256) 8 rrc).writeLE (sp + 248) 8
          rrl).writeLE (sp + 544) 8 rrp).writeLE (sp - 8) 8 6212549).readLE (sp + K) 8 := by
      intro K hK
      refine hMF.readLE _ _ ?_
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      Nat.reducePow]
    all_goals first
      | omega
      | (rw [rm _ (by omega)]
         simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
           Nat.reducePow]
         omega)
  all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true,
      getD_cons_zero, or_self, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  all_goals first
    | exact subE8 (by omega) (by omega)
    | exact h5
    | exact h14
    | (simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, r984])
    | rfl

end FvModexp.Amd64.W2Pro
