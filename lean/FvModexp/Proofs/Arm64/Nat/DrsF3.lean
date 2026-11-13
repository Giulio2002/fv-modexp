import FvModexp.Proofs.Arm64.Nat.DrsFRel3
import FvModexp.Proofs.Arm64.Nat.DrsNorm
import FvModexp.Proofs.Arm64.Nat.DrsSN3
import FvModexp.Proofs.Arm64.Nat.DrsSN
import FvModexp.Proofs.Arm64.Nat.DrsPathB
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Arm64.Nat.WinIn

/-!
# `divRecursiveStep` (arm64), final block segment 3: `qhat.norm()`, `qhatv := stk.nat(3n)`, `clear(qhatv)` (natdiv.go:864-866)

`f3n`: `AF2` → `qhat.norm()` (`norm7`) → `len` spilled at `SP'+200` → `CALL (*stack).nat(3n)` (`NF3`);
`f3s`: `NF3` → the call (`snSum`, `t3F_post`) → `qhatv` spilled (`SP'+160/144/320`) → `clear(qhatv)` (`f3m`) → `AF3`.
Adapted from DrsB3N/DrsB3S/DrsB3C.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the own store of segment 3a: `len(qhat.norm())` -/
@[reducible] def isF3a (s : State) : List (Nat × Nat) := [(s.sp.toNat - 200, s.sp.toNat - 192)]

/-- the own stores of segment 3b: `qhatv`'s slots -/
@[reducible] def isF3 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 256, s.sp.toNat - 248), (s.sp.toNat - 240, s.sp.toNat - 232), (s.sp.toNat - 80, s.sp.toNat - 72)]

set_option maxHeartbeats 16000000 in
/-- `NF3` from `AF2` and the store of `len(qhat.norm())` (pure) -/
theorem nf3_mk {R : RtInv} {c : Cx} {s S X : State} {Lk : List (Nat × Nat)} {bk j qn : Nat} {Z U : List Nat}
    (hA : AF2 R c s Lk bk S j Z U)
    (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.st) (h1 : X.regs 1 = BitVec.ofNat 64 (3 * c.vl))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rF3n) (hF2 : MemFrame S.mem X.mem (isF3a s)) (hreg : X.mem.regions = S.mem.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 200) 8 = qn)
    (hqle : qn ≤ c.vl / 2 + 1) (hqv : natVal S.mem c.t0 qn = natVal S.mem c.t0 (c.vl / 2 + 1))
    (hqN : NatNorm S.mem c.t0 qn) : NF3 R c s Lk bk X j Z U qn := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame S.mem X.mem (fw s) := hF2.mono fun x n ho => by
    simp only [fw, winA, isF3a, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF2.readLE _ _ (by simp only [win, isF3a, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → X.mem.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  refine ⟨hpc, hsp, h28, h29, h18, h0, h1, h30, hcr, Ev.own hcr hA.ev hF hreg, Fp.own hcr hA.fp hF,
    hA.bd.frame hF2 (by simp only [FixOut, isF3a, outside_cons, outside_nil, and_true]; omega)
      (by simp only [FOut, isF3a, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw), hA.jB, hA.li,
    by rw [limbs_congr (rt _ _ (Nat.le_refl _) (Nat.le_refl _))]; exact hA.qk,
    by rw [limbs_congr (rd _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk, hqle, ?_, ?_, ⟨e1⟩, hA.bud⟩
  · show X.mem.readLE c.t0 (8 * qn) = X.mem.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [rt _ _ (Nat.le_refl _) (by omega), rt _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hqv
  · rcases hqN with h | h
    · exact Or.inl h
    · right; rw [rt _ _ (by omega) (by omega)]; exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from the exit of `qhat.norm()` (`0x1baa2c`) to `CALL (*stack).nat(3n)` -/
theorem f3x (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State)
    (j : Nat) (Z U : List Nat) (hA : AF2 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ X qn, NF3 R c s Lk bk X j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q)
    (P : State) (n' : Nat) (hpc : P.pc = BitVec.ofNat 64 nExit7) (hm : P.mem = S.mem)
    (h1 : P.regs 1 = BitVec.ofNat 64 n') (hsp : P.sp = s.sp - 400#64) (h28 : P.regs 28 = s.regs 28)
    (h29 : P.regs 29 = s.sp - 408#64) (h18 : P.regs 18 = s.regs 18) (hle : n' ≤ c.vl / 2 + 1)
    (hv : natVal S.mem c.t0 n' = natVal S.mem c.t0 (c.vl / 2 + 1)) (hN : NatNorm S.mem c.t0 n') :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hst48 : c.st + 24 ≤ 2 ^ 48 := hA.ev.sok.2.2.2.1
  have haccT : S.mem.accessible c.st 24 true = true := hA.ev.sok.2.2.1
  have r1 : S.mem.readLE (s.sp.toNat - 216) 8 = c.vl / 2 + 1 := hsl.q0c
  have r2 : S.mem.readLE (s.sp.toNat - 184) 8 = c.vl := hsl.nn
  have r3 : S.mem.readLE (s.sp.toNat + 32) 8 = c.st := hsl.s4
  have hn1 : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hn2 : (BitVec.ofNat 64 (c.vl / 2 + 1)).toNat = c.vl / 2 + 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsh : BitVec.ofNat 64 c.vl <<< 1 = BitVec.ofNat 64 (2 * c.vl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have had : BitVec.ofNat 64 (2 * c.vl) + BitVec.ofNat 64 c.vl = BitVec.ofNat 64 (3 * c.vl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have had' : BitVec.ofNat 64 c.vl + BitVec.ofNat 64 (2 * c.vl) = BitVec.ofNat 64 (3 * c.vl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hst : BitVec.ofNat 64 c.st + 8#64 = BitVec.ofNat 64 (c.st + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus_run [r1, r2, r3, hn1, hn2, hsh, had, hst] until [segAddr Extracted.program StackNat.fn]
  refine k _ n' (nf3_mk hA rfl rfl ?_ ?_ ?_ ?_ ?_ rfl (by rw [← hm]; unfold isF3a; janus_frame) (by rw [← hm]; simp) ?_ hle hv hN)
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact had'
  · exact h28
  · exact h29
  · exact h18
  · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **final block segment 3a**: `AF2` → `qhat.norm()` → `CALL (*stack).nat(3n)` -/
theorem f3n (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State)
    (j : Nat) (Z U : List Nat) (hA : AF2 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ X qn, NF3 R c s Lk bk X j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hsl := hA.bd.sl
  have hpc := hA.pc; have hsp := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hsl.q0p; have r2 := hsl.q0l
  janus_run [r1, r2] until [nHead7]
  have hacc : S.mem.accessible c.t0 (8 * (c.vl / 2 + 1)) false = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_read_of_write _ hcr.t0acc
  refine norm7 impl (s.regs 30) S.mem c.t0 (c.vl / 2 + 1) (natVal S.mem c.t0 (c.vl / 2 + 1)) _ Q ?_ (by omega)
    hcr.t048 hacc ?_ (c.vl / 2 + 1) _ (Nat.le_refl _) rfl ?_ rfl (fun _ _ _ _ => rfl) rfl rfl
  · intro P n' hpc' hm' h1' hsp' hS' hle' hv' hN'
    refine f3x impl R c s Lk bk S j Z U hA Q k P n' hpc' hm' h1' (by rw [hsp']) ?_ ?_ ?_ hle' hv' hN'
    · rw [hS' 28 (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h28
    · rw [hS' 29 (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h29
    · rw [hS' 18 (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h18
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the final block's `clear(qhatv)` call, from the call state `X` -/
theorem f3m (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hT : TF3 R c s Lk bk M j Z U qn) (Q : State → Prop)
    (k : ∀ S', AF3 R c s Lk bk S' j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.qv s M)) (h1 : X.regs 1 = BitVec.ofNat 64 (8 * (3 * c.vl)))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rF3c) (hF3 : MemFrame M X.mem (isF3 s)) (hreg : X.mem.regions = M.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 80) 8 = c.qv s M) (e2 : X.mem.readLE (s.sp.toNat - 256) 8 = 3 * c.vl)
    (e3 : X.mem.readLE (s.sp.toNat - 240) 8 = 3 * c.vl) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hT.cr
  have hev := hT.ev
  obtain ⟨hce, hsv, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, ⟨-, -, hqh, hqw, -⟩, ⟨-, -, huh, huw, -⟩,
    ⟨-, -, hvh, hvw, -, -, -⟩, -⟩ := hcr.pre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, hga, hgr, -, -⟩ := hce'
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have h0' : 408 ≤ s.sp.toNat := by omega
  have hx : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hF : MemFrame M X.mem (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, isF3, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hev hF hreg
  have hFpX := Fp.own hcr hT.fp hF
  have rd3 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, isF3, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : BdF c s X.mem Z := hT.bd.frame hF3
    (by simp only [FixOut, isF3, outside_cons, outside_nil, and_true]; omega)
    (by simp only [FOut, isF3, outside_cons, outside_nil, and_true]; omega) (rd3 _ _ hvw)
    (rd3 _ _ (huw.of_sub (by omega) (by omega))) (rd3 _ _ hqw)
  have hQ3X : QF3 s X.mem qn :=
    ⟨by rw [hF3.readLE _ _ (by simp only [isF3, outside_cons, outside_nil, and_true]; omega)]; exact hT.q3.s200⟩
  have hrg := hT.rg
  have hqvw := hrg.w
  -- the header is kept by the own stores
  have hsto : Outside c.st 24 (win s c.W 96) := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have eW0 : stW X.mem c.st = stW M c.st := rd3 _ _ (hsto.of_sub (by omega) (by omega))
  have eC0 : stCap X.mem c.st = stCap M c.st := rd3 _ _ (hsto.of_sub (by omega) (by omega))
  have hqvX : c.qv s X.mem = c.qv s M := by simp only [Cx.qv]; rw [eW0]
  have hlc := hev.sok.2.2.2.2.2.1
  have hl2 := hT.fp.len
  have hn : 0 < stCap M c.st := by simp only [Cx.l1, StackNat.rnd] at hl2; omega
  obtain ⟨-, -, hacA, -⟩ := hev.sok.2.2.2.2.1 hn
  have hqin : c.qv s M + 8 * (3 * c.vl) ≤ stW M c.st + 8 * stCap M c.st := by
    simp only [Cx.qv, Cx.l1, StackNat.rnd] at hl2 ⊢; omega
  have hdw : c.qv s M + 8 * (3 * c.vl) ≤ s.sp.toNat - c.W ∨ s.sp.toNat + 96 ≤ c.qv s M := by
    simp only [win, outside_cons, outside_nil, and_true] at hqvw; omega
  have hq48 : c.qv s M + 8 * (3 * c.vl) ≤ 2 ^ 48 := by have := hev.sok.2.2.2.2.1 hn; omega
  refine ReachesRet.call_regions (hmc Lk bk) (by rw [hpc]) (mc_pre (dst := c.qv s M) (n := 8 * (3 * c.vl)) hce
    (by omega) hx X hsp h28 (hEvX.grd hcr) (fun a n w => hEvX.fr.accessible a n w) (by rw [h30]; decide)
    (by rw [h30]; decide) hEvX.inv (by rw [h0, BitVec.toNat_ofNat]; omega)
    (by rw [h1, BitVec.toNat_ofNat]; omega) (hsv.2.2.1 _ _ (by omega)) hq48
    (by rw [hEvX.fr.accessible, ← hev.fr.accessible]
        exact Memory.accessible_mono _ hacA (by simp only [Cx.qv]; omega) hqin) hrg.h hdw) ?_
  intro T hT' ⟨junk, f, v, m, ex, ep, hs, hMF, hLF, hinv', hzr⟩ hrg'
  subst hs
  have e0 : (X.regs 0).toNat = c.qv s M := by rw [h0, BitVec.toNat_ofNat]; omega
  have e1' : (X.regs 1).toNat = 8 * (3 * c.vl) := by rw [h1, BitVec.toNat_ofNat]; omega
  rw [e0, e1'] at hMF hLF hzr
  rw [show calleeStack X 4096 2 = winA X 4096 24 by simp only [calleeStack, winA]] at hMF
  have hS : ∀ x n, Outside x n (winA s c.W 96) → Outside x n (winA X 4096 24) := fun _ _ ho =>
    winA_in ho hspn (by omega) (by omega) (by omega)
  have hloc := (arr_loc (l := c.l1 s) hev (by simp only [Cx.l1]; omega) (Nat.le_refl _) hqin).out
  have hst : Outside c.st 24 [(c.qv s M, c.qv s M + 8 * (3 * c.vl))] := by
    have := hrg.st; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  rw [h28] at hinv'
  have hreg' : m.regions = X.mem.regions := by rw [← hrg']; rfl
  have hEvT : Ev R c s Lk bk m := Ev.callN hcr hEvX hMF hLF hS hloc.1 hloc.2 hst hinv' hreg'
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr hEvX hMF hLF hS hst
  have kp : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n (c.qv s M) (8 * (3 * c.vl)) →
      m.readLE x n = M.readLE x n := by
    intro x n hh hw' hap
    rw [Held.readLE2 hh hMF hLF (hS _ _ (by simp only [win, winA, outside_cons, outside_nil, and_true] at hw' ⊢; omega))
      (by unfold Apart at hap; simp only [outside_cons, outside_nil, and_true]; omega)]
    exact rd3 x n hw'
  have kv := kp _ _ (hx.held hvh) hvw hrg.v.symm
  have kt : m.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
      (apS hrg.u.symm (by omega) (by omega))
  have ku : m.readLE c.up (8 * c.u1) = M.readLE c.up (8 * c.u1) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
      (apS hrg.u.symm (by omega) (by omega))
  have kq := kp _ _ (hx.held hqh) hqw hrg.q.symm
  have kt0 := kp _ _ (hev.ext.held hcr.t0h) hcr.t0w hrg.t0.symm
  have ft : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → m.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd_sub kt0 h1 h2
  have hfo : FixOut s (R.rt ++ winA X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) := by
    refine fixOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at hqvw ⊢; omega
  have hio : FOut s (R.rt ++ winA X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) := by
    refine fOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [FOut, win, outside_cons, outside_nil, and_true] at hqvw ⊢; omega
  have hhi : HiOut s (R.rt ++ winA X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win hqvw (by omega) (by omega))
  have hBdT : BdF c s m Z := hBdX.frame hMF hfo hio (kv.trans (rd3 _ _ hvw).symm)
    (kt.trans (rd3 _ _ (huw.of_sub (by omega) (by omega))).symm) (kq.trans (rd3 _ _ hqw).symm)
  have eqv : c.qv s m = c.qv s M := by simp only [Cx.qv]; rw [eW, eW0]
  have hmT : (retStateX X junk [] f v m ex ep).mem = m := rfl
  refine k _ ⟨?_, hsp, ?_, ?_, ?_, hcr, hEvT, Fp.hdr hFpX eW eL eC, hBdT, hT.jB, hT.li,
    by rw [hmT, limbs_congr kt0]; exact hT.qk, by rw [hmT, limbs_congr ku]; exact hT.uk, hT.qle, ?_, ?_,
    hQ3X.frame hMF hhi h0', ⟨?_, ?_, ?_⟩, by rw [hmT, eqv]; exact hrg, FL.hdr (FL.hdr hT.fl eW0 eC0) eW eC,
    by rw [hmT, eqv]; exact FvModexp.Expmc.readLE_zeroed hzr, hT.bud⟩
  · rw [hT']; simp only [h30]
  · simp only [retStateX, callRegs, h28]; simp
  · simp only [retStateX, callRegs, h29]; simp
  · simp only [retStateX, callRegs, h18]; simp
  · rw [hmT]; show m.readLE c.t0 (8 * qn) = m.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [ft _ _ (Nat.le_refl _) (by have := hT.qle; omega), ft _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hT.qv
  · rcases hT.qN with h | h
    · exact Or.inl h
    · right; rw [hmT, ft _ _ (by omega) (by have := hT.qle; omega)]; exact h
  · rw [hmT, eqv, hMF.readLE _ _ (hhi.of_sub (by omega) (by omega)), e1]
  · rw [hmT, hMF.readLE _ _ (hhi.of_sub (by omega) (by omega)), e2]
  · rw [hmT, hMF.readLE _ _ (hhi.of_sub (by omega) (by omega)), e3]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **final block segment 3b**: `NF3` → `stk.nat(3n)` → `clear(qhatv)` → `AF3` -/
theorem f3s (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmc' : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (X : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hN : NF3 R c s Lk bk X j Z U qn) (Q : State → Prop)
    (k : ∀ L' b' S', AF3 R c s L' b' S' j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hN.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hN.sp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hst64 : c.st < 2 ^ 64 := by have := hN.ev.sok.2.2.2.1; omega
  have hn64 : 3 * c.vl < 2 ^ 64 := by omega
  have e30 : (BitVec.ofNat 64 rF3n : BitVec 64).toNat = 0x1baa4c := by decide
  refine ReachesRet.call_regions (snSum impl hap R hgr hmc hwb bk Lk (BitVec.ofNat 64 c.st)
    (BitVec.ofNat 64 (3 * c.vl))) hN.pc ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [hN.r30, e30]; exact raS impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]; exact ⟨hN.r0, hN.r1, trivial⟩
  case pre =>
    rw [tNat hst64, tNat hn64]
    exact sn3_pre hcr hN.ev hN.fp hspn hN.r28 (by have := hN.bud; omega)
  rw [tNat hst64, tNat hn64] at hq
  obtain ⟨hr0, hr1, hr2, L', b', hT3⟩ := t3F_post hN hspn hq hrg
  have hTpc : T.pc = BitVec.ofNat 64 rF3n := by rw [hT, hN.r30]
  have hTsp : T.sp = s.sp - 400#64 := f1.trans hN.sp
  have h28 : T.regs 28 = s.regs 28 := f2.trans hN.r28
  have h29 : T.regs 29 = s.sp - 408#64 := f3.trans hN.r29
  have h18 : T.regs 18 = s.regs 18 := f4.trans hN.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn' : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hT3.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hl3 := lsl3_ofNat (3 * c.vl) (by omega)
  have hne : (BitVec.ofNat 64 (3 * c.vl) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hq48 : c.qv s T.mem < 2 ^ 64 := by
    have hl := hT3.fp.len; have hlc := hT3.ev.sok.2.2.2.2.2.1
    have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
    have hn : 0 < stCap T.mem c.st := by omega
    obtain ⟨-, -, -, h48⟩ := hT3.ev.sok.2.2.2.2.1 hn
    simp only [Cx.qv]; omega
  clear hq hT f1 f2 f3 f4 hrg
  janus_run [hl3, hne] until [cA "runtime.memclrNoHeapPointers"]
  refine f3m impl R hmc' c s L' b' T.mem j Z U qn hT3 Q (k L' b') _ rfl rfl ?_ ?_ ?_ ?_ ?_ rfl
    (by unfold isF3; janus_frame) (by simp) ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact hr0
  · exact h28
  · exact h29
  · exact h18
  all_goals (try dsimp only)
  all_goals (repeat (first | rw [Memory.readLE_writeLE_self] | rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]))
  all_goals (rw [Nat.mod_eq_of_lt (by omega)])

end FvModexp.Arm64.DivRec
