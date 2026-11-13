import FvModexp.Proofs.Arm64.Nat.DrsA3
import FvModexp.Proofs.Arm64.Nat.WinIn

/-!
# `divRecursiveStep` (arm64), loop body segment 3b: `qhatv := stk.nat(3n)`, `clear(qhatv)` (natdiv.go:829-830)

* `T3`: the memory facts right after `stk.nat(3n)` (stack length `l1 + rnd(3n)`, `qhatv` at `stW + 8·l1`).
* `b3m`: the `clear(qhatv)` call from its call state (`memclrNoHeapPointers`, `24n` bytes) → `A3`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the memory facts after `stk.nat(3n)` -/
structure T3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  cr : Cr R c s
  ev : Ev R c s Lk bk M
  fp : Fp R c s Lk M (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : Bd c s M j Z
  bs : Bs c s M j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  qk : Asm.limbs M c.t0 (c.vl / 2 + 1) = (c.R s j U).1
  uk : Asm.limbs M c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal M c.t0 qn = natVal M c.t0 (c.vl / 2 + 1)
  qN : NatNorm M c.t0 qn
  q3 : Q3 c s M qn
  rg : Rg R c s Lk (c.qv s M) (8 * (3 * c.vl))
  fl : FL R c s Lk M
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + mulC (c.l1 s + StackNat.rnd (3 * c.vl)) (c.vl / 2 + 1) (c.vl / 2 - 1) ≤ bk

/-- a range of the stack's array from a length `≥` the entry length is a `Loc` range -/
theorem arr_loc {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory} {l a n : Nat}
    (h : Ev R c s Lk bk M) (hl : stLen s.mem c.st ≤ l) (h1 : stW M c.st + 8 * l ≤ a)
    (h2 : a + n ≤ stW M c.st + 8 * stCap M c.st) : Loc R c s a n := by
  rcases h.sarr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · left; rw [e1, e2] at h2; rw [e1] at h1; omega
  · right
    exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩

/-- the own stores of segment 3b: `qhatv`'s slots -/
@[reducible] def is3 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 248, s.sp.toNat - 240), (s.sp.toNat - 232, s.sp.toNat - 224), (s.sp.toNat - 72, s.sp.toNat - 64)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the `clear(qhatv)` call, from the call state `X` -/
theorem b3m (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hT : T3 R c s Lk bk M j Z U qn) (Q : State → Prop)
    (k : ∀ S', A3 R c s Lk bk S' j Z U qn → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.qv s M)) (h1 : X.regs 1 = BitVec.ofNat 64 (8 * (3 * c.vl)))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 r3c) (hF3 : MemFrame M X.mem (is3 s)) (hreg : X.mem.regions = M.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 72) 8 = c.qv s M) (e2 : X.mem.readLE (s.sp.toNat - 248) 8 = 3 * c.vl)
    (e3 : X.mem.readLE (s.sp.toNat - 232) 8 = 3 * c.vl) :
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
    simp only [fw, winA, is3, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hev hF hreg
  have hFpX := Fp.own hcr hT.fp hF
  have rd3 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, is3, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : Bd c s X.mem j Z := hT.bd.frame hF3
    (by simp only [FixOut, is3, outside_cons, outside_nil, and_true]; omega)
    (by simp only [IOut, is3, outside_cons, outside_nil, and_true]; omega) (rd3 _ _ hvw)
    (rd3 _ _ (huw.of_sub (by omega) (by omega))) (rd3 _ _ hqw)
  have hBsX : Bs c s X.mem j := hT.bs.frame hF3 (by simp only [BOut, is3, outside_cons, outside_nil, and_true]; omega)
  have hQ3X : Q3 c s X.mem qn :=
    ⟨by rw [hF3.readLE _ _ (by simp only [is3, outside_cons, outside_nil, and_true]; omega)]; exact hT.q3.s208,
      by rw [hF3.readLE _ _ (by simp only [is3, outside_cons, outside_nil, and_true]; omega)]; exact hT.q3.s256⟩
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
  have hio : IOut s (R.rt ++ winA X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) := by
    refine iOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [IOut, win, outside_cons, outside_nil, and_true] at hqvw ⊢; omega
  have hbo : BOut s (R.rt ++ winA X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) := by
    refine bOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [BOut, win, outside_cons, outside_nil, and_true] at hqvw ⊢; omega
  have hhi : HiOut s (R.rt ++ winA X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win hqvw (by omega) (by omega))
  have hBdT : Bd c s m j Z := hBdX.frame hMF hfo hio (kv.trans (rd3 _ _ hvw).symm)
    (kt.trans (rd3 _ _ (huw.of_sub (by omega) (by omega))).symm) (kq.trans (rd3 _ _ hqw).symm)
  have eqv : c.qv s m = c.qv s M := by simp only [Cx.qv]; rw [eW, eW0]
  have hmT : (retStateX X junk [] f v m ex ep).mem = m := rfl
  refine k _ ⟨?_, hsp, ?_, ?_, ?_, hcr, hEvT, Fp.hdr hFpX eW eL eC, hBdT, hBsX.frame hMF hbo, hT.jB, hT.li,
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

end FvModexp.Arm64.DivRec
