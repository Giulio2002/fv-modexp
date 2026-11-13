import FvModexp.Proofs.Amd64.NatQ.DrsFRel3

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF3.lean `f3m`; adapted from Amd64/NatQ/DrsB3S.lean)
# `divRecursiveStep` (amd64), final block segment 3b: `clear(qhatv)` (natdiv.go:866)

`f3m`: from the entry of `runtime.memclrNoHeapPointers` (called at `0x5f02b1` with `qhatv`, `8·3n` bytes; `qhatv`'s
slots `0x90/0x80/0x138(SP)` = `r-248`, `r-264`, `r-80` stored) to its return `0x5f02b6` (`AF3`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the own stores of segment 3b: the return slot and `qhatv`'s slots -/
@[reducible] def isF3c (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392), ((s.regs 4).toNat - 264, (s.regs 4).toNat - 256),
    ((s.regs 4).toNat - 248, (s.regs 4).toNat - 240), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the `clear(qhatv)` call, from the callee entry `X` -/
theorem f3m (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hT : TF3 R c s Lk bk M j Z U qn) (Q : State → Prop)
    (k : ∀ S', AF3 R c s Lk bk S' j Z U qn → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers"))
    (hsp : X.regs 4 = s.regs 4 - 400#64) (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.qv s M)) (h3 : X.regs 3 = BitVec.ofNat 64 (8 * (3 * c.vl)))
    (hF3 : MemFrame M X.mem (isF3c s)) (hreg : X.mem.regions = M.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rF3c)
    (e1 : X.mem.readLE ((s.regs 4).toNat - 80) 8 = c.qv s M) (e2 : X.mem.readLE ((s.regs 4).toNat - 264) 8 = 3 * c.vl)
    (e3 : X.mem.readLE ((s.regs 4).toNat - 248) 8 = 3 * c.vl) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hT.cr
  have hev := hT.ev
  have hpre := hcr.pre
  have hce := hpre.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  obtain ⟨-, -, hqh, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvw, -, -, -⟩ := hpre.va
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hx : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hF : MemFrame M X.mem (fw s) := hF3.mono fun x n ho => by
    simp only [fw, win, isF3c, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hev hF hreg
  have hFpX := Fp.own hcr hT.fp hF
  have rd3 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, isF3c, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : BdF c s X.mem Z := hT.bd.frame hF3
    (by simp only [FixOut, isF3c, outside_cons, outside_nil, and_true]; omega)
    (by simp only [FOut, isF3c, outside_cons, outside_nil, and_true]; omega) (rd3 _ _ hvw)
    (rd3 _ _ (huw.of_sub (by omega) (by omega))) (rd3 _ _ hqw)
  have hQ3X : QF3 s X.mem qn :=
    ⟨by rw [hF3.readLE _ _ (by simp only [isF3c, outside_cons, outside_nil, and_true]; omega)]; exact hT.q3.s200⟩
  have hrg := hT.rg
  have hqvw := hrg.w
  -- the header is kept by the own stores
  have hsto : Outside c.st 24 (win s c.W 96) := hpre.sti.2.1
  have eW0 : stW X.mem c.st = stW M c.st := rd3 _ _ (hsto.of_sub (by omega) (by omega))
  have eC0 : stCap X.mem c.st = stCap M c.st := rd3 _ _ (hsto.of_sub (by omega) (by omega))
  have hlc := hev.sok.2.2.2.2.2.1
  have hl2 := hT.fp.len
  have hn : 0 < stCap M c.st := by simp only [Cx.l1, StackNat.rnd] at hl2; omega
  obtain ⟨-, -, hacA, -⟩ := hev.sok.2.2.2.2.1 hn
  have hqin : c.qv s M + 8 * (3 * c.vl) ≤ stW M c.st + 8 * stCap M c.st := by
    simp only [Cx.qv, Cx.l1, StackNat.rnd] at hl2 ⊢; omega
  have hq48 : c.qv s M + 8 * (3 * c.vl) ≤ 2 ^ 48 := by have := hev.sok.2.2.2.2.1 hn; omega
  have e0 : (X.regs 0).toNat = c.qv s M := by rw [h0, BitVec.toNat_ofNat]; omega
  have e3' : (X.regs 3).toNat = 8 * (3 * c.vl) := by rw [h3, BitVec.toNat_ofNat]; omega
  refine ReachesRet.call_regions (hmc Lk bk) hpc (mcL_pre hce (by omega) hpre.sv hx X (by omega) h14
    (hEvX.grd hcr) (fun a n w => hEvX.fr.accessible a n w) (by rw [hspn, hra]; decide) hx15 hdf hEvX.inv e0 e3'
    (by omega) hq48 (by rw [hEvX.fr.accessible, ← hev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacA (by simp only [Cx.qv]; omega) hqin) hrg.h hqvw) ?_
  intro T hT' ⟨junk, f, xx, yh, m, zh, kr, hs, hMF, hLF, hinv', hzr⟩ hrg'
  subst hs
  rw [e0, e3'] at hMF hLF hzr
  have hMFw : MemFrame X.mem m (R.rt ++ win X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) :=
    hMF.mono fun x n ho => by
      simp only [calleeStack64, win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  have hS : ∀ x n, Outside x n (win s c.W 96) → Outside x n (win X 4096 24) := fun x n ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
  have hloc := (arr_loc (l := c.l1 s) hev (by simp only [Cx.l1]; omega) (Nat.le_refl _) hqin).out
  have hst : Outside c.st 24 [(c.qv s M, c.qv s M + 8 * (3 * c.vl))] := by
    have := hrg.st; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  rw [h14] at hinv'
  have hreg' : m.regions = X.mem.regions := by rw [← hrg']; rfl
  have hEvT : Ev R c s Lk bk m := Ev.callN hcr hEvX hMFw hLF hS hloc.1 hloc.2 hst hinv' hreg'
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr hEvX hMFw hLF hS hst
  have kp : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n (c.qv s M) (8 * (3 * c.vl)) →
      m.readLE x n = M.readLE x n := by
    intro x n hh hw' hap
    rw [Held.readLE2 hh hMFw hLF (hS _ _ hw')
      (by unfold Apart at hap; simp only [outside_cons, outside_nil, and_true]; omega)]
    exact rd3 x n hw'
  have kv := kp _ _ (hx.held hvh) hvw hrg.v.symm
  have kt : m.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
      (apL hrg.u.symm (by omega) (by omega))
  have ku : m.readLE c.up (8 * c.u1) = M.readLE c.up (8 * c.u1) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
      (apL hrg.u.symm (by omega) (by omega))
  have kq := kp _ _ (hx.held hqh) hqw hrg.q.symm
  have kt0 := kp _ _ (hev.ext.held hcr.t0h) hcr.t0w hrg.t0.symm
  have ft : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → m.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd_sub kt0 h1 h2
  have hfo : FixOut s (R.rt ++ win X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) := by
    refine fixOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at hqvw ⊢; omega
  have hio : FOut s (R.rt ++ win X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) := by
    refine fOut_callee hout (by omega) (by omega) hspn (by omega) ?_
    simp only [FOut, win, outside_cons, outside_nil, and_true] at hqvw ⊢; omega
  have hhi : HiOut s (R.rt ++ win X 4096 24 ++ [(c.qv s M, c.qv s M + 8 * (3 * c.vl))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win hqvw (by omega) (by omega))
  have hBdT : BdF c s m Z := hBdX.frame hMFw hfo hio (kv.trans (rd3 _ _ hvw).symm)
    (kt.trans (rd3 _ _ (huw.of_sub (by omega) (by omega))).symm) (kq.trans (rd3 _ _ hqw).symm)
  have eqv : c.qv s m = c.qv s M := by simp only [Cx.qv]; rw [eW, eW0]
  have hmT : (retState64 X junk [] f xx yh m zh kr).mem = m := rfl
  refine k _ ⟨?pc, ?sp, ?r5, ?r14, hfs, hdf, ?x15, hcr, hEvT, Fp.hdr hFpX eW eL eC, hBdT, hT.jB,
    hT.li, by rw [hmT, limbs_congr kt0]; exact hT.qk, by rw [hmT, limbs_congr ku]; exact hT.uk, hT.qle, ?qv, ?qN,
    hQ3X.frame hMFw hhi h0', ⟨?v1, ?v2, ?v3⟩, by rw [hmT, eqv]; exact hrg, FL.hdr (FL.hdr hT.fl eW0 eC0) eW eC,
    by rw [hmT, eqv]; exact FvModexp.Expmc.readLE_zeroed hzr, bud_cap (eC.trans eC0) hT.bud⟩
  case pc => rw [hT']; simp only [retAddrOf]; rw [hspn, hra]
  case sp =>
    simp only [retState64, callRegs64_apply, ite_true]
    exact sp_ret400 hspn (by omega)
  case r5 =>
    simp only [retState64, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 =>
    simp only [retState64, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case x15 => simp only [retState64, ite_true]; exact hx15
  case qv =>
    rw [hmT]; show m.readLE c.t0 (8 * qn) = m.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [ft _ _ (Nat.le_refl _) (by have := hT.qle; omega), ft _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hT.qv
  case qN =>
    rcases hT.qN with h | h
    · exact Or.inl h
    · right; rw [hmT, ft _ _ (by omega) (by have := hT.qle; omega)]; exact h
  case v1 => rw [hmT, eqv, hMFw.readLE _ _ (hhi.of_sub (by omega) (by omega)), e1]
  case v2 => rw [hmT, hMFw.readLE _ _ (hhi.of_sub (by omega) (by omega)), e2]
  case v3 => rw [hmT, hMFw.readLE _ _ (hhi.of_sub (by omega) (by omega)), e3]

end FvModexp.Amd64.Q.DivRec
