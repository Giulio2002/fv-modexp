import FvModexp.Proofs.Amd64.NatQ.DrsF4D

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF4C.lean; adapted from Amd64/NatQ/DrsB4C.lean)
# `divRecursiveStep` (amd64), final block segment 4: the call `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:867)

`b4cF`: from the entry `X` of `nat.mul` (called at `0x5f0314`; memory = `AF3`'s + the own stores `is4`): the call
(`mulSum`, return `rF4 = 0x5f0319`), `mul_pre` / `mul_postF` → the continuation at the return state with `McF` at
the model state `Cx.sF0` and the result registers `qhatv`, `|PF|`, `3n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the call `nat.mul` from its entry state `X` -/
theorem b4cF (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (ns : List String)
    (hns : ns.contains DivLarge.drsFn = false)
    (hcode : CodeIn64 ((Extracted.program.onlySegments ns).link impl) (LibDrs.program.link impl))
    (hmul : MulHypQE impl R ns mulWX64)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qn : Nat)
    (hA : AF3 R c s Lk bk S j Z U qn)
    (Q : State → Prop)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 (segAddr Extracted.program FvModexp.Amd64.Q.NatMul.fn))
    (hsp : X.regs 4 = s.regs 4 - 400#64) (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.qv s S.mem)) (h3 : X.regs 3 = BitVec.ofNat 64 (3 * c.vl))
    (h1 : X.regs 1 = BitVec.ofNat 64 (3 * c.vl)) (h7 : X.regs 7 = BitVec.ofNat 64 c.st)
    (h6 : X.regs 6 = BitVec.ofNat 64 c.t0) (h8 : X.regs 8 = BitVec.ofNat 64 qn)
    (h9 : X.regs 9 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (hF4 : MemFrame S.mem X.mem (is4 s)) (hreg : X.mem.regions = S.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rF4)
    (a1 : X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.vp)
    (a2 : X.mem.readLE ((s.regs 4).toNat - 384) 8 = c.vl / 2 - 1)
    (a3 : X.mem.readLE ((s.regs 4).toNat - 376) 8 = c.vc)
    (k : ∀ T : State, T.rip = BitVec.ofNat 64 rF4 → T.regs 4 = s.regs 4 - 392#64 → T.regs 5 = s.regs 4 - 8#64 →
      T.regs 14 = s.regs 14 → T.fsBase = s.fsBase → T.df = false → T.xmm 15 = 0#128 →
      T.regs 0 = BitVec.ofNat 64 (c.qv s S.mem) → T.regs 3 = BitVec.ofNat 64 (c.PF s U).length →
      T.regs 1 = BitVec.ofNat 64 (3 * c.vl) →
      (∃ L' b', McF R c s L' b' T.mem j Z U (c.qv s S.mem) (c.sF0 s U)) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  have hv9 := hpre.v9.1; have hvc40 := hpre.vc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hA' := AF3.own hA X.mem hF4 hreg
  have hsto : Outside c.st 24 (win s c.W 96) := hpre.sti.2.1
  have eW : stW X.mem c.st = stW S.mem c.st :=
    hF4.readLE _ _ (by simp only [win, is4, outside_cons, outside_nil, and_true] at hsto ⊢; omega)
  have eqv : c.qv s X.mem = c.qv s S.mem := by simp only [Cx.qv]; rw [eW]
  have hqle := hA.qle
  have hst48 : c.st + 24 ≤ 2 ^ 48 := hA.ev.sok.2.2.2.1
  have ht48 := hcr.t048
  have hq48 : c.qv s S.mem < 2 ^ 48 := by
    have hl := hA.fp.len; have hlc := hA.ev.sok.2.2.2.2.2.1
    have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
    have hn : 0 < stCap S.mem c.st := by omega
    obtain ⟨-, -, -, h48⟩ := hA.ev.sok.2.2.2.2.1 hn
    simp only [Cx.qv]; omega
  have t1 := tNat (by omega : c.qv s S.mem < 2 ^ 64); have t2 := tNat (by omega : 3 * c.vl < 2 ^ 64)
  have t3 := tNat (by omega : c.st < 2 ^ 64); have t4 := tNat (by omega : c.t0 < 2 ^ 64)
  have t5 := tNat (by omega : qn < 2 ^ 64); have t6 := tNat (by omega : c.vl / 2 + 1 < 2 ^ 64)
  rw [← eqv] at t1 h0
  refine ReachesRet.call_regions (mulSum impl hap R ns hcode hmul c.Hq bk Lk c.vp (c.vl / 2 - 1) c.vc) hpc
    ⟨?ra, hx15, hdf, ?pre⟩ (fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_)
  case ra => simp only [regSP]; rw [hspn, hra]; exact raF4 impl hap ns hns
  case pre =>
    rw [h0, h1, h7, h6, h8, h9, t1, t2, t3, t4, t5, t6, hspn]
    refine ⟨by rw [show (s.regs 4).toNat - 400 + 8 = (s.regs 4).toNat - 392 by omega]; exact a1,
      by rw [show (s.regs 4).toNat - 400 + 16 = (s.regs 4).toNat - 384 by omega]; exact a2,
      by rw [show (s.regs 4).toNat - 400 + 24 = (s.regs 4).toNat - 376 by omega]; exact a3, ?_⟩
    exact mul_pre (X := X) hcr hA'.ev hA'.fp hA'.rg hqle hspn h14 hfs (mulW64_le_X (by omega) (by omega))
      (by show 30792 + 400 ≤ c.W; omega) (by have h := hA'.bud; dsimp only at h; omega)
  rw [h0, h1, h7, h6, h8, h9, t1, t2, t3, t4, t5, t6] at hq
  obtain ⟨hTfs, hTdf, hr0, hr3, hr1, L', b', hmc⟩ := mul_postF (X := X) hA' rfl hspn h14 (by show 30792 + 400 ≤ c.W; omega) hq hrg
  refine k T ?_ ?_ (f5.trans h5) (f14.trans h14) (hTfs.trans hfs) (hTdf.trans hdf) (f15.trans hx15)
    (by rw [hr0]; exact congrArg _ eqv) hr3 hr1 ⟨L', b', by rw [← eqv]; exact hmc⟩
  · rw [hT]; simp only [retAddrOf]; rw [hspn, hra]
  · rw [f4]; exact sp_ret400 hspn (by omega)

end FvModexp.Amd64.Q.DivRec
