import FvModexp.Proofs.Amd64.NatQ.DrsCRel
import FvModexp.Proofs.Amd64.NatQ.DrsMulP

set_option autoImplicit false

/-! (amd64 twin (asm s48) of Arm64/NatQ/DrsMulQ.lean)
# `divRecursiveStep` (amd64), loop body: after `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831; pure)

* `zero_sub`: a sub-range of a zero range reads `0`.
* `P_eq`: the model's product `Cx.P` is the normalised product of the operands' values.
* `mul_post`: divmc's amd64 `Q.NatMul.MPost` (with its exact-write clause `Exact`) → `Mc` at the model state `Cx.st0`;
  the result registers are `qhatv`'s array, `|P|`, `3n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem zero_sub {m : Memory} {a N x k : Nat} (h : m.readLE a N = 0) (h1 : a ≤ x) (h2 : x + k ≤ a + N) :
    m.readLE x k = 0 := by
  have e : N = (x - a) + (k + (a + N - (x + k))) := by omega
  have ex : a + (x - a) = x := by omega
  rw [e, Janus.Arm64.Memory.readLE_add, Janus.Arm64.Memory.readLE_add, ex] at h
  have hp : 0 < 256 ^ (x - a) := Nat.pow_pos (by decide)
  have hq : 0 < 256 ^ k := Nat.pow_pos (by decide)
  have h3 : 256 ^ (x - a) * (m.readLE x k + 256 ^ k * m.readLE (x + k) (a + N - (x + k))) = 0 := by omega
  rcases Nat.mul_eq_zero.1 h3 with h4 | h4
  · omega
  · omega

/-- the operand facts of the product (model side) -/
theorem P_eq {c : Cx} {s : State} {M : Memory} {j qn : Nat} {U : List Nat}
    (hqk : Asm.limbs M c.t0 qn = c.q0 s j U) (hvk : M.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl))
    (hB : c.vl / 2 - 1 ≤ c.vl) :
    c.P s j U = Mdl.norm (Mdl.toL (natVal M c.t0 qn * natVal M c.vp (c.vl / 2 - 1)) (qn + (c.vl / 2 - 1))) := by
  simp only [Cx.P, Mdl.mulI, Cx.V]
  rw [Asm.limbs_take _ _ _ _ hB, ← hqk, Asm.length_limbs, Asm.length_limbs, Asm.val_limbs, Asm.val_limbs]
  simp only [natVal, Asm.lv]
  rw [rd_sub hvk (Nat.le_refl _) (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **after the product**: memory facts at the model state `Cx.st0` -/
theorem mul_post {R : RtInv} {c : Cx} {s S X T : State} {Lk : List (Nat × Nat)} {bk j qn W' : Nat}
    {Z U : List Nat} (hA : A3 R c s Lk bk S j Z U qn) (hm : X.mem = S.mem)
    (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14) (hkW : W' + 400 ≤ c.W)
    (hpost : Q.NatMul.MPost R bk c.Hq Lk W' (c.qv s X.mem) (3 * c.vl) c.st c.t0 qn (c.vl / 2 + 1) c.vp
      (c.vl / 2 - 1) c.vc X T)
    (hreg : T.mem.regions = X.mem.regions) :
    T.fsBase = X.fsBase ∧ T.df = X.df ∧
    T.regs 0 = BitVec.ofNat 64 (c.qv s S.mem) ∧ T.regs 3 = BitVec.ofNat 64 (c.P s j U).length ∧
      T.regs 1 = BitVec.ofNat 64 (3 * c.vl) ∧
      ∃ L' b', Mc R c s L' b' T.mem j Z U (c.qv s S.mem) (c.st0 s j U) := by
  have hcr := hA.cr; have hev := hA.ev; have hfp := hA.fp; have hrg := hA.rg
  have hW := hcr.hW; have hWg := drsW64_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1; have hqle := hA.qle
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hpre := hcr.pre
  have hvl9 := hpre.v9.1; have hvlc := hpre.vlc
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
  obtain ⟨-, -, hqh, hqo, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huo, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvo, -, hvch, -⟩ := hpre.va
  obtain ⟨-, hstw, -, -⟩ := hpre.sti
  obtain ⟨-, -, hvcf, -⟩ := hpre.stl
  obtain ⟨hqs, -⟩ := hpre.sq
  obtain ⟨hus, -⟩ := hpre.su
  obtain ⟨hvs, -⟩ := hpre.sv2
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨hfs, hdf, p', l', c', hr0, hr3, hr1, hval0, hnorm, -, -, -, L', b', hx, hbud, hinv, -, hor, -, hex,
    hsbL, -, -⟩ := hpost
  simp only [hm] at hbud hval0 hor hex hsbL hreg
  rw [h14] at hinv
  have hlen := hfp.len
  have hr3' : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
  have hlc : stLen S.mem c.st ≤ stCap S.mem c.st := hev.sok.2.2.2.2.2.1
  -- the operand values and `qhat.norm()` = the model's
  have hqk0 : Asm.limbs S.mem c.t0 qn = c.q0 s j U := Asm.limbs_norm hA.qk hA.qv hA.qN
  have hqn : (c.q0 s j U).length = qn := by rw [← hqk0, Asm.length_limbs]
  -- where `qhatv` lies
  have hqin : c.qv s S.mem + 8 * (3 * c.vl) ≤ stW S.mem c.st + 8 * stCap S.mem c.st := by
    simp only [Cx.qv]; omega
  have hn : 0 < stCap S.mem c.st := by omega
  obtain ⟨hal8, -, hacA, harr48⟩ := hev.sok.2.2.2.2.1 hn
  have hloc : Loc R c s (c.qv s S.mem) (8 * (3 * c.vl)) :=
    arr_loc (l := c.l1 s) hev (by simp only [Cx.l1]; omega) (Nat.le_refl _) hqin
  have hvc : Apart c.vp (8 * c.vc) (c.qv s S.mem) (8 * (3 * c.vl)) := by
    rcases hloc with ⟨h1, h2⟩ | ⟨hin, hap⟩
    · unfold Apart at hvcf ⊢; omega
    · exact fresh_apart hvch hin hap
  have rt0 := hrg.t0
  obtain ⟨e0, e2, hval, hMF, hLF⟩ := hex (by omega) (by unfold Apart at rt0; omega) (by unfold Apart at hvc; omega)
  subst e0 e2
  -- frames
  have hMF' : MemFrame S.mem T.mem (R.rt ++ win X W' 88 ++
      ([(c.qv s S.mem, c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1)))] ++ stkWs S.mem c.st)) := by
    rw [← List.append_assoc]; exact hMF
  have h0 : 408 ≤ (s.regs 4).toNat := by omega
  have ffw := hfp.fw; have ft0 := hfp.ft0; have fu := hfp.fu; have fv := hfp.fv; have fq := hfp.fq
  rw [← hlen] at ffw ft0 fu fv fq
  have hws504 : Outside ((s.regs 4).toNat - 408) 504
      ([(c.qv s S.mem, c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1)))] ++ stkWs S.mem c.st) := by
    have a1 := out504 (hrg.w.of_sub (Nat.le_refl _) (by omega : c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1)) ≤
      c.qv s S.mem + 8 * (3 * c.vl))) (by omega) (by omega)
    have a3 := out504 hstw (by omega) (by omega)
    have a4 := out504 ffw (by omega) (by omega)
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at a1 a3 a4 ⊢
    refine ⟨a1, a3, ?_⟩
    rw [show stW S.mem c.st + 8 * stCap S.mem c.st = stW S.mem c.st + 8 * stLen S.mem c.st +
      8 * (stCap S.mem c.st - stLen S.mem c.st) by omega]; exact a4
  obtain ⟨fo, io, bo⟩ := fo504 hws504 h0
  have hhi : HiOut s (R.rt ++ win X W' 88 ++
      ([(c.qv s S.mem, c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1)))] ++ stkWs S.mem c.st)) :=
    hiOut_callee hout (by omega) (by omega) hsp (by omega) (hws504.of_sub (by omega) (by omega))
  have kp : ∀ {x n : Nat}, Held R Lk x n → Outside x n (win s c.W 96) →
      Apart x n (c.qv s S.mem) (8 * (qn + (c.vl / 2 - 1))) → Apart x n c.st 24 →
      Apart x n (stW S.mem c.st + 8 * stLen S.mem c.st) (8 * (stCap S.mem c.st - stLen S.mem c.st)) →
      T.mem.readLE x n = S.mem.readLE x n := fun hh hw' h1 h3 h4 => by
    refine keepRd hcr hsp hkW (by omega) hMF' hLF hh hw' ?_
    unfold Apart at h1 h3 h4
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    omega
  have rgu := hrg.u; have rgv := hrg.v; have rgq := hrg.q
  have kv : T.mem.readLE c.vp (8 * c.vl) = S.mem.readLE c.vp (8 * c.vl) :=
    kp (hext.held hvh) hvo (apR rgv.symm (Nat.le_refl _) (by omega)) hvs fv.symm
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → T.mem.readLE x n = S.mem.readLE x n := fun x n h1 h2 =>
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apR (apL rgu.symm h1 h2) (Nat.le_refl _) (by omega))
      (apL hus h1 h2) (apL fu.symm h1 h2)
  have kz : T.mem.readLE c.qp (8 * c.ql) = S.mem.readLE c.qp (8 * c.ql) :=
    kp (hext.held hqh) hqo (apR rgq.symm (Nat.le_refl _) (by omega)) hqs fq.symm
  have kt0 : T.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = S.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) :=
    kp (hev.ext.held hcr.t0h) hcr.t0w (apR rt0.symm (Nat.le_refl _) (by omega)) hcr.t0st ft0.symm
  -- the buffer
  have hz0 := hA.z0
  have hvT : natVal T.mem (c.qv s S.mem) (qn + (c.vl / 2 - 1)) =
      natVal S.mem c.t0 qn * natVal S.mem c.vp (c.vl / 2 - 1) := by
    rcases hval with h | ⟨h1, h2⟩
    · exact h
    · rw [h2, h1]; exact zero_sub hz0 (Nat.le_refl _) (by omega)
  have hzT : T.mem.readLE (c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1))) (8 * (3 * c.vl - (qn + (c.vl / 2 - 1)))) = 0 := by
    rw [kp (hrg.h.sub (by omega) (by omega)) (hrg.w.of_sub (by omega) (by omega)) (by unfold Apart; omega)
      (apL hrg.st.symm (by omega) (by omega)) (by unfold Apart; simp only [Cx.qv]; omega)]
    exact zero_sub hz0 (by omega) (by omega)
  have hP := P_eq (s := s) (j := j) (U := U) hqk0 hA.bd.vk (by omega)
  have hvl : natVal S.mem c.t0 qn * natVal S.mem c.vp (c.vl / 2 - 1) < 2 ^ (64 * (qn + (c.vl / 2 - 1))) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (natVal_lt _ _ _) (natVal_lt _ _ _)
  have hl' : l' = (c.P s j U).length := by
    rw [hP, ← Asm.len_mul hval0 hnorm hvl, Asm.length_limbs]
  -- the environment
  have hS : ∀ x k, Outside x k (win s c.W 96) → Outside x k (win X W' 88) := fun x k ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hsp]; omega
  have hloc2 : Loc R c s (c.qv s S.mem) (8 * (qn + (c.vl / 2 - 1))) := by
    rcases hloc with ⟨h1, h2⟩ | ⟨hin, hap⟩
    · left; exact ⟨h1, by omega⟩
    · right; exact ⟨hin.sub (Nat.le_refl _) (by omega), ApartAll.sub' hap (Nat.le_refl _) (by omega)⟩
  have hlo := hloc2.out
  have hl : stLen s.mem c.st ≤ stLen S.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' T.mem := Ev.callS hcr hev hl hMF hLF hS hlo.1 hlo.2 hx hinv hsbL hreg
  have hFp := Fp.callS hcr hev hfp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsbL
  have hBd : Bd c s T.mem j Z := hA.bd.frame hMF'
    (fixOut_callee hout (by omega) (by omega) hsp (by omega) fo)
    (iOut_callee hout (by omega) (by omega) hsp (by omega) io) kv (ku _ _ (by omega) (by omega)) kz
  have hBs : Bs c s T.mem j := hA.bs.frame hMF' (bOut_callee hout (by omega) (by omega) hsp (by omega) bo)
  have huT : Asm.limbs T.mem c.up c.u1 = c.U2 s j U := by
    rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega))]; exact hA.uk
  refine ⟨hfs, hdf, hr0, by rw [hr3, hl'], hr1, L', b', hcr, hEv, hFp, hBd, hBs, hA.jB, hA.li,
    by rw [hqn]; exact hA.q3.frame hMF' hhi h0,
    ⟨hx.held hrg.h, hrg.w, hrg.g, hrg.fs, hrg.st, hrg.gA, hrg.q, hrg.u, hrg.v, hrg.t0⟩,
    by rw [hqn, limbs_congr (rd_sub kt0 (Nat.le_refl _) (by omega))]; exact hqk0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Asm.limbs T.mem (c.qv s S.mem) (3 * c.vl) = c.P s j U ++ List.replicate (3 * c.vl - (c.P s j U).length) 0
    rw [hP]; exact Asm.buf_mul (by omega) hvT hzT
  · show _ = (c.U2 s j U).drop (j - c.vl / 2)
    rw [← huT, Asm.limbs_drop]
  · show _ = (c.U2 s j U).take (j - c.vl / 2)
    rw [← huT, Asm.limbs_take _ _ _ _ (by omega)]
  · have hmc : mulCQ qn (c.vl / 2 - 1) ≤ mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) := mulCQ_mono hqle (Nat.le_refl _)
    have := hA.bud
    omega
  · rw [hMF.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hacA (by simp only [Cx.qv]; omega) hqin
  · exact hloc
  · simp only [Cx.qv]; omega
  · exact FL.callS hcr hev hA.fl (by rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega) (by rw [hlen]; omega) hx hsbL

end FvModexp.Amd64.Q.DivRec
