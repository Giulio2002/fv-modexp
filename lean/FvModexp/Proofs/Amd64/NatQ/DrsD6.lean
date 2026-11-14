import FvModexp.Proofs.Amd64.NatQ.DrsSegD
import FvModexp.Proofs.Amd64.NatQ.DrsCallS

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsD6.lean)
# `divRecursiveStep` (amd64), end of an iteration: `addTo(z[j-B:], qhat)` (natdiv.go:851)

`d6`: from the `CALL addTo` entry `X` (`RSP = r - 400`, return `0x5f00ad`; `Mc … stG` at the pre-call state `T`)
→ `addTo` (`AddTo.ens` on `LibDrs`, via `atSum`) → its return `0x5f00ad` (`rD6`) with `G` (quotient / dividend = `Cx.BS`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
/-- the return site `0x5f00ad` is admissible for `addTo`'s program -/
theorem raD6 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) rD6 := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := AddTo.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0x82d (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

/-- the dividend after the step, from `uu`'s and `u[:j-B]`'s memory -/
theorem uk_step {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} {M : Memory} (hcr : Cr R c s)
    (hli : c.LI s j Z U) (hjB : c.vl / 2 < j)
    (hlk : Asm.limbs M c.up (j - c.vl / 2) = (c.U2 s j U).take (j - c.vl / 2))
    (hwk : Asm.limbs M (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) = (c.sT s j U).1) :
    Asm.limbs M c.up c.u1 = (c.BS s j Z U).2 := by
  have hul := hli.2.2.2.1
  have := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hli.2.2.2.2.2.2.2; omega
  have hvu := hcr.vu1
  rw [(bs_eq hcr hli hjB).2, ← List.take_append_drop (j - c.vl / 2) (Asm.limbs M c.up c.u1),
    Asm.limbs_take _ _ _ _ (by omega), Asm.limbs_drop, hlk, hwk]
  simp only [Cx.U2]
  rw [Mdl.take_upd_of_le _ _ _ _ (by omega) (by omega), Mdl.upd_eq_of_full _ _ _ (by omega)]
  rw [← hwk, Asm.length_limbs]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`addTo(z[j-B:], qhat)`** from its callee entry → `G` -/
theorem d6 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv : Nat)
    (Q : State → Prop) (T : State) (hmc0 : Mc R c s Lk bk T.mem j Z U qv (c.stG s j U))
    (X : State) (hpc : X.rip = BitVec.ofNat 64 addToC) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.qp + 8 * (j - c.vl / 2))) (h3 : X.regs 3 = BitVec.ofNat 64 (c.ql - (j - c.vl / 2)))
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.qc - (j - c.vl / 2))) (h7 : X.regs 7 = BitVec.ofNat 64 c.t0)
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.q0 s j U).length) (h8 : X.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (hFR : MemFrame T.mem X.mem (isR s)) (hreg0 : X.mem.regions = T.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rD6)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rD6 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      G R c s L' b' T' j Z U → ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hqa, hq48, hqh, hqw, hqg⟩ := hpre.qa
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvw, -, -, -⟩ := hpre.va
  have hqlc := hpre.qlc; have hqc40 := hpre.qc40; have hvl9 := hpre.v9.1
  have hqu := hpre.qu; have hqv' := hpre.qv; have hqs := hpre.sq.1; have hqtl := hpre.tl.1
  have hqp8 : c.qp % 8 = 0 := hpre.stl.2.2.2.2.2
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have hroom := (room hcr).1
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame T.mem X.mem (is1 s) := hFR.mono fun x n ho => by
    simp only [isR, is1, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := Mc.own1 hmc0 hF1 hreg0
  have hev := hmc.ev
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 4232 48 := Ev.callEnv hcr hev hspn h14 hfs (by omega) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hev.fr.accessible]
  -- the quotient digit fits `z[j-B:]`
  have hqn : (c.stF s j U).qhat.length = (c.q0 s j U).length := by
    have := hmc.qk; rw [← this, Asm.length_limbs]
  have hfit := q_fit hcr hmc.li hjB
  rw [hqn] at hfit
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have t0w := hcr.t0w; have t0q := hcr.t0q
  simp only [win, outside_cons, outside_nil, and_true] at hqw t0w
  have tz := tN (by omega : c.qp + 8 * (j - c.vl / 2) < 2 ^ 64)
  have tl := tN (by omega : c.ql - (j - c.vl / 2) < 2 ^ 64)
  have tc := tN (by omega : c.qc - (j - c.vl / 2) < 2 ^ 64)
  have tx := tN (by have := hcr.t048; omega : c.t0 < 2 ^ 64)
  have tn := tN (by omega : (c.q0 s j U).length < 2 ^ 64)
  refine ReachesRet.call_regions (atSum impl hap R hmv bk Lk (X.regs 0) (X.regs 3) (X.regs 1) (X.regs 7)
    (X.regs 6) (X.regs 8)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, ⟨g1, g2, hq⟩⟩ hrgT => ?_)
  case ra => rw [show (X.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raD6 impl hap
  case pre =>
    rw [h0, h3, h1, h7, h6, tz, tl, tc, tx, tn]
    refine ⟨hce', by omega, by omega, by omega, fun _ => ⟨by omega, hext.held (hqh.sub (by omega) (by omega)),
      by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hqa (by omega) (by omega), by omega⟩, ?_, by omega,
      (by rw [hXacc]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hcr.t0acc (Nat.le_refl _) (by omega))),
      by have := hcr.t048; omega, (hev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega), ?_, fun _ => ?_, ?_, ?_,
      by rw [h14]; exact hev.inv⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · unfold Apart at t0q ⊢; omega
    · rw [h14]; unfold Apart at hqg ⊢; omega
    · rw [hfs]; unfold Apart at hqtl ⊢; omega
  rw [h0, h3, h7, h6, tz, tl, tx, tn] at hq
  obtain ⟨hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = X.mem.regions := hrgT
  rw [h14] at hinv
  -- the environment (as in `Mc.callN`, the written range being `z[j-B:]`)
  have hS : ∀ x m, Outside x m (win s c.W 96) → Outside x m (win X 4232 48) := fun x m ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
  have hst' : Outside c.st 24 [(c.qp + 8 * (j - c.vl / 2), c.qp + 8 * (j - c.vl / 2) + 8 * (c.ql - (j - c.vl / 2)))] := by
    unfold Apart at hqs; simp only [outside_cons, outside_nil, and_true]; omega
  have hF' : MemFrame X.mem T'.mem (R.rt ++ win X 4232 48 ++
      [(c.qp + 8 * (j - c.vl / 2), c.qp + 8 * (j - c.vl / 2) + 8 * (c.ql - (j - c.vl / 2)))] ++ stkWs X.mem c.st) :=
    hMF.mono fun x m ho => by simp only [outside_append] at ho ⊢; exact ⟨ho.1.1, ho.1.2⟩
  have hL' : LiveFrame X.mem T'.mem Lk
      ([(c.qp + 8 * (j - c.vl / 2), c.qp + 8 * (j - c.vl / 2) + 8 * (c.ql - (j - c.vl / 2)))] ++ stkWs X.mem c.st) :=
    SubVW.liveFrame_mono hLF fun x m ho => by simp only [outside_append] at ho; exact ho.1
  have hsb := stackBack_keep hcr hev hMF hLF hS hst' hx
  obtain ⟨eW, -, eC⟩ := hdr_keep hcr hev hMF hLF hS hst'
  have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hmc.fp.len]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' T'.mem := Ev.callS hcr hev hl hF' hL' hS
    (fun _ _ h => ws_qp h (by omega) (by omega))
    (fun _ _ _ h => ws_qp0 h (by omega) (by omega))
    hx hinv hsb hreg
  have hFp : Fp R c s L' T'.mem (c.l1 s + StackNat.rnd (3 * c.vl)) :=
    Fp.callS hcr hev hmc.fp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  have hFL : FL R c s L' T'.mem := Rg.ext (FL.hdr hmc.fl eW eC) hx
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.qp + 8 * (j - c.vl / 2), c.qp + 8 * (j - c.vl / 2) + 8 * (c.ql - (j - c.vl / 2)))] →
      T'.mem.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have kv : T'.mem.readLE c.vp (8 * c.vl) = X.mem.readLE c.vp (8 * c.vl) :=
    rk _ _ (hext.held hvh) hvw (by unfold Apart at hqv'; simp only [outside_cons, outside_nil, and_true]; omega)
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → T'.mem.readLE x n = X.mem.readLE x n := fun x n h1 h2 =>
    rk _ _ (hext.held (huh.sub h1 h2)) (huw.of_sub h1 h2)
      (by unfold Apart at hqu; simp only [outside_cons, outside_nil, and_true]; omega)
  have hwl : FixOut s [(c.qp + 8 * (j - c.vl / 2), c.qp + 8 * (j - c.vl / 2) + 8 * (c.ql - (j - c.vl / 2)))] := by
    simp only [FixOut, outside_cons, outside_nil, and_true]; omega
  have hfo := fixOut_callee (k := 4232) (a := 48) hout (by omega) (by omega) hspn (by omega) hwl
  have hhi : HiOut s (R.rt ++ win X 4232 48 ++
      [(c.qp + 8 * (j - c.vl / 2), c.qp + 8 * (j - c.vl / 2) + 8 * (c.ql - (j - c.vl / 2)))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  -- the quotient after the call
  have hzv := Asm.addTo_model X.mem T'.mem _ _ _ _ hfit hval
  have hzk : Asm.limbs T'.mem c.qp c.ql = (c.BS s j Z U).1 := by
    rw [Asm.limbs_upd (m := X.mem) (j := j - c.vl / 2) (k := c.ql - (j - c.vl / 2)) (by omega)
      (fun i hi hi2 => rk _ _ (hext.held (hqh.sub (by omega) (by omega)))
        (by simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hzv, (bs_eq hcr hmc.li hjB).1,
      hmc.bd.zk, ← hmc.bd.zk, Asm.limbs_drop, hmc.qk]
  have huk : Asm.limbs T'.mem c.up c.u1 = (c.BS s j Z U).2 := by
    rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega))]
    exact uk_step hcr hmc.li hjB hmc.lk hmc.wk
  refine k T' (by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]) L' b'
    ⟨by rw [f1, hsp]; bv_omega, f2.trans h5, f3.trans h14, g1.trans hfs, g2.trans hdf, f4.trans hx15, hcr, hEv,
      hFp, hFL, hmc.bd.sl.frame hMF hfo, ?_, ?_, by rw [kv]; exact hmc.bd.vk,
      by rw [ku _ _ (by omega) (by omega)]; exact hmc.bd.utl, hzk, huk, hmc.li, hjB,
      bud_cap eC (Nat.le_trans hmc.bud hb)⟩
  · rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hmc.bd.sj
  · rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hmc.q3.s256

end FvModexp.Amd64.Q.DivRec
