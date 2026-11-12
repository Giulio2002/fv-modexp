import FvModexp.Proofs.Arm64.Nat.DrsCRel
import FvModexp.Proofs.Arm64.Nat.DrsMulP

/-!
# `divRecursiveStep` (arm64), loop body: after `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:831; pure)

* `zero_sub`: a sub-range of a zero range reads `0`.
* `mul_val`: the result registers are `qhatv`'s array with length `|P|` (`P = Cx.P` = the model's normalised product), and
  the `3n`-word buffer is `P ++ 0…` (`Cx.st0`'s `buf`).
* `mul_post`: `nat.mul`'s post (`MulPostL ∧ ExactR`, divmc's `MPost` + `Exact`) → `Mc` at the model state `Cx.st0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

theorem zero_sub {m : Memory} {a N x k : Nat} (h : m.readLE a N = 0) (h1 : a ≤ x) (h2 : x + k ≤ a + N) :
    m.readLE x k = 0 := by
  have e : N = (x - a) + (k + (a + N - (x + k))) := by omega
  have ex : a + (x - a) = x := by omega
  rw [e, Memory.readLE_add, Memory.readLE_add, ex] at h
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

set_option maxHeartbeats 16000000 in
/-- **after the product**: memory facts at the model state `Cx.st0` -/
theorem mul_post {R : RtInv} {c : Cx} {s S X T : State} {Lk : List (Nat × Nat)} {bk j qn stkM aboveM : Nat}
    {Z U : List Nat} (hA : A3 R c s Lk bk S j Z U qn) (hm : X.mem = S.mem) (hsp : X.sp.toNat = s.sp.toNat - 400)
    (h28 : X.regs 28 = s.regs 28) (hk : stkM ≤ mulWX) (ha : aboveM ≤ 88)
    (hpost : EvenHyp.MulPostL R bk (mulC (stLen X.mem c.st) qn (c.vl / 2 - 1)) Lk stkM aboveM (c.qv s X.mem)
        (3 * c.vl) c.st c.t0 qn c.vp (c.vl / 2 - 1) X T ∧
      ExactR R Lk (winA X stkM aboveM) (qn + (c.vl / 2 - 1)) (c.qv s X.mem) (3 * c.vl) c.st c.t0 (c.vl / 2 + 1)
        c.vp c.vc (natVal X.mem c.t0 qn * natVal X.mem c.vp (c.vl / 2 - 1)) X T)
    (hreg : T.mem.regions = X.mem.regions) :
    T.regs 0 = BitVec.ofNat 64 (c.qv s X.mem) ∧ T.regs 1 = BitVec.ofNat 64 (c.P s j U).length ∧
      T.regs 2 = BitVec.ofNat 64 (3 * c.vl) ∧
      ∃ L' b', Mc R c s L' b' T.mem j Z U (c.qv s X.mem) (c.st0 s j U) := by
  have hcr := hA.cr; have hev := hA.ev; have hfp := hA.fp; have hrg := hA.rg
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1; have hqle := hA.qle
  have hk' : stkM ≤ 30208 := hk
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, -, -, -, -, -, -, hvlc, -, -, ⟨hvl9, -⟩, -, -, -,
    ⟨-, -, hqh, hqo, -⟩, ⟨-, -, huh, huo, -⟩, ⟨-, -, hvh, hvo, -, hvch, -⟩, -, -, -,
    ⟨-, hstw, -, -⟩, ⟨-, -, hvcf, -⟩, ⟨hqs, -⟩, ⟨hus, -⟩, ⟨hvs, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨⟨p', l', c', hr0, hr1, hr2, L', b', hNOF, ⟨hx, hbud, hinv⟩, hsbL, -, -, -⟩, hex⟩ := hpost
  rw [hm] at hbud hNOF hreg hex ⊢
  rw [h28] at hinv
  have hlen := hfp.len
  have hr3 : 3 * c.vl ≤ StackNat.rnd (3 * c.vl) := by simp only [StackNat.rnd]; omega
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
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
  rw [hm] at hval hMF hLF
  -- the result
  have hp' : p' = c.qv s S.mem := by
    rcases hNOF.2.2.2.2.2 with ⟨h1, -⟩ | ⟨h1, -, -⟩
    · exact h1
    · have hc0 : 0 < c' := by omega
      obtain ⟨-, -, -, h48⟩ := hNOF.2.2.2.2.1 hc0
      have := congrArg BitVec.toNat (hr0.symm.trans e0)
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by simp only [Cx.qv]; omega)] at this; exact this
  rw [hp'] at hNOF
  -- frames
  have hMF' : MemFrame S.mem T.mem (R.rt ++ winA X stkM aboveM ++
      ([(c.qv s S.mem, c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1)))] ++ stkWs S.mem c.st)) := by
    rw [← List.append_assoc]; exact hMF
  have h0 : 408 ≤ s.sp.toNat := by omega
  have ffw := hfp.fw; have ft0 := hfp.ft0; have fu := hfp.fu; have fv := hfp.fv; have fq := hfp.fq
  rw [← hlen] at ffw ft0 fu fv fq
  have hws504 : Outside (s.sp.toNat - 408) 504
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
  have hhi : HiOut s (R.rt ++ winA X stkM aboveM ++
      ([(c.qv s S.mem, c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1)))] ++ stkWs S.mem c.st)) :=
    hiOut_callee hout (by omega) (by omega) hsp (by omega) (hws504.of_sub (by omega) (by omega))
  have kp : ∀ {x n : Nat}, Held R Lk x n → Outside x n (win s c.W 96) →
      Apart x n (c.qv s S.mem) (8 * (qn + (c.vl / 2 - 1))) → Apart x n c.st 24 →
      Apart x n (stW S.mem c.st + 8 * stLen S.mem c.st) (8 * (stCap S.mem c.st - stLen S.mem c.st)) →
      T.mem.readLE x n = S.mem.readLE x n := fun hh hw' h1 h3 h4 => by
    refine keepRd hcr hsp (by omega) (by omega) hMF' hLF hh hw' ?_
    unfold Apart at h1 h3 h4
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    omega
  have rgu := hrg.u; have rgv := hrg.v; have rgq := hrg.q
  have kv : T.mem.readLE c.vp (8 * c.vl) = S.mem.readLE c.vp (8 * c.vl) :=
    kp (hext.held hvh) hvo (apR' rgv.symm (Nat.le_refl _) (by omega)) hvs fv.symm
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → T.mem.readLE x n = S.mem.readLE x n := fun x n h1 h2 =>
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apR' (apS rgu.symm h1 h2) (Nat.le_refl _) (by omega))
      (apS hus h1 h2) (apS fu.symm h1 h2)
  have kz : T.mem.readLE c.qp (8 * c.ql) = S.mem.readLE c.qp (8 * c.ql) :=
    kp (hext.held hqh) hqo (apR' rgq.symm (Nat.le_refl _) (by omega)) hqs fq.symm
  have kt0 : T.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = S.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) :=
    kp (hev.ext.held hcr.t0h) hcr.t0w (apR' rt0.symm (Nat.le_refl _) (by omega)) hcr.t0st ft0.symm
  -- the buffer
  have hz0 := hA.z0
  have hvT : natVal T.mem (c.qv s S.mem) (qn + (c.vl / 2 - 1)) =
      natVal S.mem c.t0 qn * natVal S.mem c.vp (c.vl / 2 - 1) := by
    rcases hval with h | ⟨h1, h2⟩
    · exact h
    · rw [h2, h1]; exact zero_sub hz0 (Nat.le_refl _) (by omega)
  have hzT : T.mem.readLE (c.qv s S.mem + 8 * (qn + (c.vl / 2 - 1))) (8 * (3 * c.vl - (qn + (c.vl / 2 - 1)))) = 0 := by
    rw [kp (hrg.h.sub (by omega) (by omega)) (hrg.w.of_sub (by omega) (by omega)) (by unfold Apart; omega)
      (apS hrg.st.symm (by omega) (by omega)) (by unfold Apart; simp only [Cx.qv]; omega)]
    exact zero_sub hz0 (by omega) (by omega)
  have hP := P_eq (s := s) (j := j) (U := U) hqk0 hA.bd.vk (by omega)
  have hvl : natVal S.mem c.t0 qn * natVal S.mem c.vp (c.vl / 2 - 1) < 2 ^ (64 * (qn + (c.vl / 2 - 1))) := by
    rw [Nat.mul_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (natVal_lt _ _ _) (natVal_lt _ _ _)
  have hl' : l' = (c.P s j U).length := by
    rw [hP, ← Asm.len_mul hNOF.1 hNOF.2.1 hvl, Asm.length_limbs]
  -- the environment
  have hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k (winA X stkM aboveM) := fun x k ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hsp]; omega
  have hloc2 : Loc R c s (c.qv s S.mem) (8 * (qn + (c.vl / 2 - 1))) := by
    rcases hloc with ⟨h1, h2⟩ | ⟨hin, hap⟩
    · left; exact ⟨h1, by omega⟩
    · right; exact ⟨hin.sub (Nat.le_refl _) (by omega), ApartAll.sub' hap (Nat.le_refl _) (by omega)⟩
  have hlo := hloc2.out
  have hsb := hsbL.toStackBack
  rw [hm] at hsb
  have hl : stLen s.mem c.st ≤ stLen S.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' T.mem := Ev.callS hcr hev hl hMF hLF hS hlo.1 hlo.2 hx hinv hsb hreg
  have hFp := Fp.callS hcr hev hfp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  have hBd : Bd c s T.mem j Z := hA.bd.frame hMF'
    (fixOut_callee hout (by omega) (by omega) hsp (by omega) fo)
    (iOut_callee hout (by omega) (by omega) hsp (by omega) io) kv (ku _ _ (by omega) (by omega)) kz
  have hBs : Bs c s T.mem j := hA.bs.frame hMF' (bOut_callee hout (by omega) (by omega) hsp (by omega) bo)
  have huT : Asm.limbs T.mem c.up c.u1 = c.U2 s j U := by
    rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega))]; exact hA.uk
  refine ⟨by rw [e0], by rw [hr1, hl'], e2, L', b', hcr, hEv, hFp, hBd, hBs, hA.jB, hA.li,
    by rw [hqn]; exact hA.q3.frame hMF' hhi h0,
    ⟨hx.held hrg.h, hrg.w, hrg.g, hrg.st, hrg.gA, hrg.q, hrg.u, hrg.v, hrg.t0⟩,
    by rw [hqn, limbs_congr (rd_sub kt0 (Nat.le_refl _) (by omega))]; exact hqk0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Asm.limbs T.mem (c.qv s S.mem) (3 * c.vl) = c.P s j U ++ List.replicate (3 * c.vl - (c.P s j U).length) 0
    rw [hP]; exact Asm.buf_mul (by omega) hvT hzT
  · show _ = (c.U2 s j U).drop (j - c.vl / 2)
    rw [← huT, Asm.limbs_drop]
  · show _ = (c.U2 s j U).take (j - c.vl / 2)
    rw [← huT, Asm.limbs_take _ _ _ _ (by omega)]
  · have hmc : mulC (stLen S.mem c.st) qn (c.vl / 2 - 1) ≤
        mulC (c.l1 s + StackNat.rnd (3 * c.vl)) (c.vl / 2 + 1) (c.vl / 2 - 1) := by
      rw [hlen]; exact mulC_mono (Nat.le_refl _) hqle (Nat.le_refl _)
    have := hA.bud
    omega
  · rw [hMF.accessible]
    exact Memory.accessible_mono _ hacA (by simp only [Cx.qv]; omega) hqin
  · exact hloc
  · simp only [Cx.qv]; omega

end FvModexp.Arm64.DivRec
