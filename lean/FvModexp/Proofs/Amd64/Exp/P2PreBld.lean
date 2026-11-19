import FvModexp.Proofs.Amd64.Exp.P2PreWb

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the callee environment inside the function (agent divmc s62; twin of
infra's `Arm64/Exp/P2PreBld`)

`guard_keep` / `tls_keep`: the `stackguard0` word and the TLS `g` slot are outside everything the function writes.
`cenv_ctx` / `callEnv_ctx`: the callee environment at `RSP_c = RSP - 184` (window `kc` below, `88` above) on a memory
`M` of a context `Ctx`. `globals_ctx`: the threshold globals and the write-barrier flag at `M`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

section
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the guard word and the TLS slot are outside everything the function writes -/
theorem gt_keep (hpre : Pre R kc b L st pw pl ws lm x xl s) {M : Memory}
    (hF : MemFrame s.mem M (AW R kc s pw pl st)) :
    M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
      M.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
  obtain ⟨⟨-, ⟨hb', -, -⟩, -, -, -, hga, hgrt, -, -, -, htrt, htw⟩, -, -, -, -, -, -, -, -, -, -, -, hpg, hpt, -, -, -,
    -, -, -, ⟨-, ⟨-, -, -, -, -, hlc, -⟩, -, hstg, -, hfg, -, -, -, -, -, -, hstt, -, hft⟩, -⟩ := hpre
  simp only [K, A, regSP] at hga htw hb'
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN, Q.NatSqr.guard, Q.NatSqr.tls] at hfg hft hpg hpt hstg hstt
  unfold Apart at hga htw hpg hpt hstg hfg hstt hft
  constructor
  · refine hF.readLE _ _ ?_
    simp only [AW, LW, stkWs, win, K, A, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hgrt, by omega⟩, by omega, by omega, by omega⟩
  · refine hF.readLE _ _ ?_
    simp only [AW, LW, stkWs, win, K, A, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨htrt, by omega⟩, by omega, by omega, by omega⟩

set_option maxRecDepth 20000 in
/-- the callee environment at `RSP_c = RSP - 184` (window `kc` below, `88` above) -/
theorem cenv_ctx (hpre : Pre R kc b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) :
    CallW.CEnv R L1 (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 184) kc 88 M := by
  obtain ⟨hgk, htk⟩ := gt_keep hpre hc.fr
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgrt, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩, -, -, -, -,
    -, -, -, -, hacc, -, -, -, -, -, -, -, -, -, -, ⟨-, ⟨-, -, hsta, -, hstl, hlc, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -⟩,
    -⟩ := hpre
  simp only [K, A, regSP, regG, stackguard0, stackguard0Offset] at hb' ha hw hout hga hg1 hg2 hg3 hLs htw
  unfold Apart at hga htw
  refine ⟨by omega, by omega, by omega, ?_, by omega, by rw [hc.fr.accessible]; exact hg2, by rw [hgk]; omega,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgrt, ?_, ?_, hro, by omega, by omega,
    by rw [hc.fr.accessible]; exact htr, by rw [htk]; exact htg, htrt, by unfold Apart; omega⟩
  · rw [hc.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · refine hc.le.liveSep (fun q hq => ?_) (fun r hr => ?_)
    · have := hLs q hq
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (by omega) (by omega)
  · refine dataLoaded_frame64 hd hc.rg hro (by simpa only [AW, List.append_assoc] using hc.fr) ?_
    intro r hr hlt
    simp only [win, LW, stkWs, K, A, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · dsimp only at hlt ⊢; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · dsimp only at hlt ⊢; rw [show pw + 24 * pl - pw = 24 * pl by omega]; exact hacc
    · dsimp only at hlt ⊢; rw [show st + 24 - st = 24 by omega]; exact hsta
    · dsimp only at hlt ⊢
      exact Janus.Arm64.Memory.accessible_mono _ (hstl (by omega)).2.2.1 (by omega) (by omega)

theorem callEnv_ctx (hpre : Pre R kc b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) : CallEnv R L1 S' stk above := by
  have hce := cenv_ctx hpre hc
  exact CallW.callEnv_of hce hsp (by rw [h14]) (by rw [hfs]) hm hstk habove (by have := hce.2.1; omega)

set_option maxRecDepth 20000 in
theorem globals_ctx (hpre : Pre R kc b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) :
    Globals R M (win S' stk above) := by
  have hK : 184 + kc ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simp only [K, regSP] at this; omega
  obtain ⟨-, -, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, hgf, -⟩, -⟩ := hpre
  have hrd : ∀ a n, Outside a n (AW R kc s pw pl st) → M.readLE a n = s.mem.readLE a n := fun a n h =>
    hc.fr.readLE a n h
  have hA : ∀ a n, RunIface.gA ≤ a → a + n ≤ RunIface.gA + 32 → Outside a n (AW R kc s pw pl st) := by
    intro a n h1 h2
    have o1 := g9.of_sub h1 h2
    have o2 := g10.of_sub h1 h2
    simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hgf
    unfold Apart at hgf
    simp only [AW, LW, stkWs, win, K, A, List.append_assoc, List.cons_append, List.nil_append, outside_append,
      outside_cons, outside_nil, and_true] at o2 ⊢
    exact ⟨o1, by omega⟩
  have hwin : ∀ a n, Outside a n (win s (K kc) A ++ [(pw, pw + 24 * pl), (st, st + 24)]) →
      Outside a n (win S' stk above) := by
    intro a n h
    simp only [win, K, A, List.cons_append, outside_cons, outside_append, outside_nil, and_true] at h ⊢
    rw [hsp]; omega
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hc.fr.accessible]; exact g8, g9, hwin _ _ g10,
    by rw [hc.fr.accessible]; exact g11, g12, hwin _ _ g13⟩
  · rw [g5, hrd _ _ (hA _ _ (by omega) (by omega)), ← g5]; exact g1
  · rw [g6, hrd _ _ (hA _ _ (by omega) (by omega)), ← g6]; exact g2
  · rw [g7, hrd _ _ (hA _ _ (by omega) (by omega)), ← g7]; exact g3
  · have e : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
        RunIface.gA := by decide
    rw [e, hrd _ _ (hA _ _ (by omega) (by omega)), ← e]; exact g4

end

end FvModexp.Amd64.P2Pre
