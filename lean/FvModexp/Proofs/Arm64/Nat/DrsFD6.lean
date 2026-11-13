import FvModexp.Proofs.Arm64.Nat.DrsFD6R
import FvModexp.Proofs.Arm64.Nat.DrsFG
import FvModexp.Proofs.Arm64.Nat.DrsD6
import FvModexp.Proofs.Arm64.Nat.DrsWs
import FvModexp.Proofs.Arm64.Nat.WinIn

/-!
# `divRecursiveStep` (arm64), final block: `addTo(z, qhat.norm())` (natdiv.go:891)

`d6F`: from the `CALL addTo` state (`0x1bacd8`, `McF` at `Cx.sGF`, `x = qhat[:n']` with `n'` the normalised length)
→ `addTo` (`atSum`) → its return `0x1bacdc` = `GF` (`z = addTo Z (norm qhat) = (finalBlock …).1`). The callee
writes `z`, so `McF` is not kept; its environment parts are rebuilt as in DrsD6 (adapted from it).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`addTo(z, qhat.norm())`** from its call state → `GF` -/
theorem d6F (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (Q : State → Prop)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 addToA) (h30 : X.regs 30 = BitVec.ofNat 64 rFD6)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.qp) (h1 : X.regs 1 = BitVec.ofNat 64 c.ql)
    (h2 : X.regs 2 = BitVec.ofNat 64 c.qc) (h3 : X.regs 3 = BitVec.ofNat 64 c.t0)
    (n' : Nat) (h4 : X.regs 4 = BitVec.ofNat 64 n') (h5 : X.regs 5 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (hsp : X.sp = s.sp - 400#64) (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64)
    (h18 : X.regs 18 = s.regs 18) (hmc : McF R c s Lk bk X.mem j Z U qv (c.sGF s U))
    (hn' : n' ≤ (c.qF s U).length) (hv' : natVal X.mem c.t0 n' = natVal X.mem c.t0 (c.qF s U).length)
    (hN' : NatNorm X.mem c.t0 n')
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rFD6 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      GF R c s L' b' T j Z U → ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hmc.cr
  have hev := hmc.ev
  obtain ⟨hce, -, -, hqlc, hqc40, -, -, -, -, -, ⟨hvl9, hql9⟩, -, -, -, ⟨hqa, hq48, hqh, hqw, hqg⟩,
    ⟨-, -, huh, huw, -⟩, ⟨-, -, hvh, hvw, -, -, -⟩, hqu, hqv', -, -, ⟨-, -, -, -, -, hqp8⟩, ⟨hqs, -⟩, -, -, -⟩ :=
    hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjB := hmc.jB
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 4240 48 := Ev.callEnv hcr hev hspn h28 (by omega) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hev.fr.accessible]
  -- the quotient digit fits `z[j-B:]`
  have hlq : Asm.limbs X.mem c.t0 n' = Mdl.norm (c.sFF s U).qhat := Asm.limbs_norm hmc.qk hv' hN'
  have hfit : n' ≤ c.ql := by
    have e := congrArg List.length hlq
    rw [Asm.length_limbs] at e
    have := q_fitF hcr hmc.li hjB
    omega
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have t0w := hcr.t0w; have t0q := hcr.t0q
  simp only [win, outside_cons, outside_nil, and_true] at hqw t0w
  have tz := tN (by omega : c.qp < 2 ^ 64)
  have tl := tN (by omega : c.ql < 2 ^ 64)
  have tc := tN (by omega : c.qc < 2 ^ 64)
  have tx := tN (by have := hcr.t048; omega : c.t0 < 2 ^ 64)
  have tn := tN (by omega : n' < 2 ^ 64)
  refine ReachesRet.call_regions (atSum impl hap R hmv bk Lk (X.regs 0) (X.regs 1) (X.regs 2) (X.regs 3)
    (X.regs 4) (X.regs 5)) hpc
    ⟨?ra, ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, ?pre⟩
    (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrgT => ?_)
  case ra =>
    have e30 : (BitVec.ofNat 64 rFD6 : BitVec 64).toNat = rFD6 := by decide
    rw [h30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case pre =>
    rw [h0, h1, h2, h3, h4, tz, tl, tc, tx, tn]
    refine ⟨hce', by omega, by omega, by omega, fun _ => ⟨by omega, hext.held (hqh.sub (by omega) (by omega)),
      by rw [hXacc]; exact Memory.accessible_mono _ hqa (by omega) (by omega), by omega⟩, ?_, by omega,
      by rw [hXacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hcr.t0acc (Nat.le_refl _) (by omega)),
      by have := hcr.t048; omega, (hev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega), ?_, fun _ => ?_, ?_,
      by rw [h28]; exact hev.inv⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · unfold Apart at t0q ⊢; omega
    · rw [h28]; unfold Apart at hqg ⊢; omega
  rw [h0, h1, h3, h4, tz, tl, tx, tn] at hq
  obtain ⟨hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T.mem.regions = X.mem.regions := hrgT
  rw [h28] at hinv
  -- the environment (as in `Mc.callN`, the written range being `z[j-B:]`)
  have hS : ∀ x m, Outside x m (winA s c.W 96) → Outside x m (winA X 4240 48) := fun _ _ ho =>
    winA_in ho hspn (by omega) (by omega) (by omega)
  have hst' : Outside c.st 24 [(c.qp, c.qp + 8 * c.ql)] := by
    unfold Apart at hqs; simp only [outside_cons, outside_nil, and_true]; omega
  have hF' : MemFrame X.mem T.mem (R.rt ++ winA X 4240 48 ++
      [(c.qp, c.qp + 8 * c.ql)] ++ stkWs X.mem c.st) :=
    hMF.mono fun x m ho => by simp only [outside_append] at ho ⊢; exact ⟨ho.1.1, ho.1.2⟩
  have hL' : LiveFrame X.mem T.mem Lk
      ([(c.qp, c.qp + 8 * c.ql)] ++ stkWs X.mem c.st) :=
    SubVW.liveFrame_mono hLF fun x m ho => by simp only [outside_append] at ho; exact ho.1
  have hsb := stackBack_keep hcr hev hMF hLF hS hst' hx
  have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hmc.fp.len]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' T.mem := Ev.callS hcr hev hl hF' hL' hS
    (fun _ _ h => ws_qp h (by omega) (by omega))
    (fun _ _ _ h => ws_qp0 h (by omega) (by omega))
    hx hinv hsb hreg
  have hFp : Fp R c s L' T.mem (c.l1 s + StackNat.rnd (3 * c.vl)) :=
    Fp.callS hcr hev hmc.fp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.qp, c.qp + 8 * c.ql)] →
      T.mem.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → T.mem.readLE x n = X.mem.readLE x n := fun x n h1 h2 =>
    rk _ _ (hext.held (huh.sub h1 h2)) (huw.of_sub h1 h2)
      (by unfold Apart at hqu; simp only [outside_cons, outside_nil, and_true]; omega)
  have hwl : FixOut s [(c.qp, c.qp + 8 * c.ql)] := by
    simp only [FixOut, outside_cons, outside_nil, and_true]; omega
  have hfo := fixOut_callee (k := 4240) (a := 48) hout (by omega) (by omega) hspn (by omega) hwl
  -- the quotient after the call
  have hzv := Asm.addTo_model X.mem T.mem _ _ _ _ hfit hval
  have hzk : Asm.limbs T.mem c.qp c.ql = (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).1 := by
    rw [hzv, hmc.bd.zk, hlq, fin_eq]
  have huk : Asm.limbs T.mem c.up c.u1 = (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).2 := by
    rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega)), hmc.wk, fin_eq]
  refine k T (by rw [hT, h30]) L' b' ⟨f1.trans hsp, f2.trans h28, f3.trans h29, f4.trans h18, hcr, hEv, hFp,
    hmc.bd.sl.frame hMF hfo, hzk, huk,
    by rw [ku _ _ (by omega) (by omega)]; exact hmc.bd.utl, hmc.li, hjB, Nat.le_trans hmc.bud hb⟩

end FvModexp.Arm64.DivRec
