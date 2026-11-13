import FvModexp.Proofs.Amd64.NatQ.DrsCallS
import FvModexp.Proofs.Amd64.NatQ.DrsRecP
import FvModexp.Proofs.Common.DivRecIdeal

set_option autoImplicit false

/-! (amd64 twin (asm s47) of Arm64/NatQ/DrsA2.lean + DrsRecQ.lean)
# `divRecursiveStep` (amd64), loop body: after the recursive call (pure)

* `Bs c s M j`: the seven argument slots of the recursive call that the rest of the iteration reads again (offsets from
  the entry `RSP` = `r`; `SP' = r - 392`): `s = B - 1` @`0x78` (`r-272`), `v[s:]` len/cap @`0xf0`/`0xf8`
  (`r-152`/`r-144`), `8·s` @`0x100` (`r-136`), `uu[s:]` cap @`0x108` (`r-128`), `v[s:]` ptr @`0x168` (`r-32`),
  `uu[s:]` ptr @`0x170` (`r-24`); `BOut`, `bOut_callee`, `fo504`.
* `keepP`: a held range apart from the callee's writes keeps its bytes over the recursive call.
* `rec_val`: the memory after the call holds the ideal callee's lists (`Mdl.blockR Mdl.recI`).
* `rec_post`: `Ev`/`Fp`/`Bd`/`Bs`, the lists and the budget after the recursive call, from `DrsPostW`.
* `A2`: the state at the return `0x5efc31` of the recursive call (`CALL 0x5efc2c`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the argument slots of the recursive call (read again by the correction loop and `nat.mul`) -/
structure Bs (c : Cx) (s : State) (M : Memory) (j : Nat) : Prop where
  b1 : M.readLE ((s.regs 4).toNat - 272) 8 = c.vl / 2 - 1
  vlen : M.readLE ((s.regs 4).toNat - 152) 8 = c.vl - c.vl / 2 + 1
  vcap : M.readLE ((s.regs 4).toNat - 144) 8 = c.vc - (c.vl / 2 - 1)
  b8 : M.readLE ((s.regs 4).toNat - 136) 8 = 8 * (c.vl / 2 - 1)
  ucap : M.readLE ((s.regs 4).toNat - 128) 8 = c.uc - (j - 1)
  vptr : M.readLE ((s.regs 4).toNat - 32) 8 = c.vp + 8 * (c.vl / 2 - 1)
  uptr : M.readLE ((s.regs 4).toNat - 24) 8 = c.up + 8 * (j - 1)

/-- `rs` avoids the argument slots -/
@[reducible] def BOut (s : State) (rs : List (Nat × Nat)) : Prop :=
  Outside ((s.regs 4).toNat - 272) 8 rs ∧ Outside ((s.regs 4).toNat - 152) 32 rs ∧
    Outside ((s.regs 4).toNat - 32) 16 rs

theorem Bs.frame {c : Cx} {s : State} {M M' : Memory} {j : Nat} {rs : List (Nat × Nat)} (h : Bs c s M j)
    (hF : MemFrame M M' rs) (ho : BOut s rs) : Bs c s M' j := by
  obtain ⟨o1, o2, o3⟩ := ho
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N → M'.readLE x n = M.readLE x n :=
    fun hA h1 h2 => hF.readLE _ _ (hA.of_sub h1 h2)
  exact ⟨by rw [r o1 (by omega) (by omega)]; exact h.b1, by rw [r o2 (by omega) (by omega)]; exact h.vlen,
    by rw [r o2 (by omega) (by omega)]; exact h.vcap, by rw [r o2 (by omega) (by omega)]; exact h.b8,
    by rw [r o2 (by omega) (by omega)]; exact h.ucap, by rw [r o3 (by omega) (by omega)]; exact h.vptr,
    by rw [r o3 (by omega) (by omega)]; exact h.uptr⟩

/-- a callee frame `R.rt ++ win S k a ++ ws` (`S`'s `RSP = r - 400`, `a ≤ 103`) avoids the argument slots when `ws`
does -/
theorem bOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside ((s.regs 4).toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ (s.regs 4).toNat)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 400) (ha : a ≤ 103) (hws : BOut s ws) :
    BOut s (R.rt ++ win S k a ++ ws) := by
  obtain ⟨w1, w2, w3⟩ := hws
  have o : ∀ x n, (s.regs 4).toNat - 408 ≤ x → x + n ≤ (s.regs 4).toNat + 96 → Outside x n R.rt :=
    fun x n h1 h2 => hout.of_sub (by omega) (by omega)
  simp only [BOut, win, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  exact ⟨⟨⟨o _ _ (by omega) (by omega), by omega⟩, w1⟩, ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w2⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w3⟩⟩

/-- ranges outside the own frame avoid every fixed, iteration and argument slot -/
theorem fo504 {s : State} {rs : List (Nat × Nat)} (h : Outside ((s.regs 4).toNat - 408) 504 rs)
    (h0 : 408 ≤ (s.regs 4).toNat) : FixOut s rs ∧ IOut s rs ∧ BOut s rs := by
  have o : ∀ x n, (s.regs 4).toNat - 408 ≤ x → x + n ≤ (s.regs 4).toNat + 96 → Outside x n rs :=
    fun x n h1 h2 => h.of_sub (by omega) (by omega)
  exact ⟨⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega),
      o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega),
      o _ _ (by omega) (by omega)⟩,
    ⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega)⟩,
    ⟨o _ _ (by omega) (by omega), o _ _ (by omega) (by omega), o _ _ (by omega) (by omega)⟩⟩

theorem out504 {s : State} {W x n : Nat} (h : Outside x n (win s W 96)) (hW : 408 ≤ W) (h0 : W ≤ (s.regs 4).toNat) :
    Outside ((s.regs 4).toNat - 408) 504 [(x, x + n)] := by
  simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega

/-- the writes of the recursive call of iteration `j` (its `z` = `qhat0` and `u = uu[s:B+n]`) -/
@[reducible] def wsR (c : Cx) (j : Nat) : List (Nat × Nat) :=
  [(c.t0, c.t0 + 8 * (c.vl / 2 + 1)), (c.up + 8 * (j - 1), c.up + 8 * (j - 1) + 8 * (c.vl + 1))]

/-- a range apart from the recursive call's writes keeps its bytes -/
theorem keepP {R : RtInv} {c : Cx} {s X X' : State} {Lk : List (Nat × Nat)} {j x n : Nat}
    (hcr : Cr R c s) (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400)
    (hF : MemFrame X.mem X'.mem (R.rt ++ win X (c.W - 400) 96 ++ (wsR c j ++ stkWs X.mem c.st)))
    (hL : LiveFrame X.mem X'.mem Lk (wsR c j ++ stkWs X.mem c.st)) (hh : Held R Lk x n)
    (hw : Outside x n (win s c.W 96)) (h1 : Apart x n c.t0 (8 * (c.vl / 2 + 1)))
    (h2 : x + n ≤ c.up + 8 * (j - 1) ∨ c.up + 8 * (j - 1) + 8 * (c.vl + 1) ≤ x) (h3 : Apart x n c.st 24)
    (h4 : Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)))
    (hlc : stLen X.mem c.st ≤ stCap X.mem c.st) :
    X'.mem.readLE x n = X.mem.readLE x n := by
  have hW := hcr.hW; have := drsW64_ge c.vl
  refine keepRd hcr hsp (by omega) (by omega) hF hL hh hw ?_
  unfold Apart at h1 h3 h4
  simp only [wsR, stkWs, outside_append, outside_cons, outside_nil, and_true]
  omega

/-! ## the lists after the recursive call (copied from Arm64/NatQ/DrsRecQ.lean; ISA-independent) -/

theorem sl_drop_limbs {M : Memory} {up u1 j B n : Nat} (hB : 1 ≤ B) (hjB : B ≤ j) (hj : j + n ≤ u1) :
    Mdl.sl ((Asm.limbs M up u1).drop (j - B)) (B - 1) (B + n - (B - 1)) = Asm.limbs M (up + 8 * (j - 1)) (n + 1) := by
  have e : Mdl.sl ((Asm.limbs M up u1).drop (j - B)) (B - 1) (B + n - (B - 1)) =
      Mdl.sl (Asm.limbs M up u1) (j - 1) (n + 1) := by
    unfold Mdl.sl; rw [List.drop_drop]; congr 2 <;> omega
  rw [e, Asm.sl_limbs _ _ _ _ _ (by omega)]

theorem drop_limbs_v {M : Memory} {vp n k : Nat} (hk : k ≤ n) :
    (Asm.limbs M vp n).drop k = Asm.limbs M (vp + 8 * k) (n - k) := by
  have : (Asm.limbs M vp n).drop k = Mdl.sl (Asm.limbs M vp n) k (n - k) := by
    unfold Mdl.sl; rw [List.take_of_length_le (by simp)]
  rw [this, Asm.sl_limbs _ _ _ _ _ (by omega)]

/-- **the lists after the recursive call** -/
theorem rec_val {M0 M M' : Memory} {up u1 vp n t0 j : Nat} {U : List Nat} (h40 : 40 ≤ n) (hjB : n / 2 < j)
    (hj : j + n ≤ u1) (huk : Asm.limbs M up u1 = U)
    (hv : M.readLE (vp + 8 * (n / 2 - 1)) (8 * (n - n / 2 + 1)) = M0.readLE (vp + 8 * (n / 2 - 1)) (8 * (n - n / 2 + 1)))
    (hq : natVal M' t0 (n / 2 + 1) =
      natVal M (up + 8 * (j - 1)) (n + 1) / natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1))
    (hr : natVal M' (up + 8 * (j - 1)) (n + 1) =
      natVal M (up + 8 * (j - 1)) (n + 1) % natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1)) :
    Asm.limbs M' t0 (n / 2 + 1) = (Mdl.blockR Mdl.recI (Asm.limbs M0 vp n) n (n / 2) j U).1 ∧
      Asm.limbs M' (up + 8 * (j - 1)) (n + 1) = (Mdl.blockR Mdl.recI (Asm.limbs M0 vp n) n (n / 2) j U).2 := by
  have e1 : Mdl.sl (U.drop (j - n / 2)) (n / 2 - 1) (n / 2 + n - (n / 2 - 1)) = Asm.limbs M (up + 8 * (j - 1)) (n + 1) := by
    rw [← huk]; exact sl_drop_limbs (by omega) (by omega) hj
  have e2 : (Asm.limbs M0 vp n).drop (n / 2 - 1) = Asm.limbs M0 (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1) := by
    rw [drop_limbs_v (by omega), show n - (n / 2 - 1) = n - n / 2 + 1 by omega]
  have ev : Mdl.val (Asm.limbs M0 (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1)) =
      natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1) := by
    rw [Asm.val_limbs]; show M0.readLE _ _ = M.readLE _ _; exact hv.symm
  unfold Mdl.blockR Mdl.recI
  rw [e1, e2, Asm.val_limbs, ev]
  simp only [List.length_replicate, Asm.length_limbs]
  refine ⟨?_, ?_⟩
  · rw [Mdl.eq_toL (Asm.Wd_limbs M' t0 (n / 2 + 1)), Asm.val_limbs, Asm.length_limbs]
    exact congrArg (Mdl.toL · (n / 2 + 1)) hq
  · rw [Mdl.eq_toL (Asm.Wd_limbs M' _ (n + 1)), Asm.val_limbs, Asm.length_limbs]
    exact congrArg (Mdl.toL · (n + 1)) hr

/-- the lists and facts after the recursive call -/
@[reducible] def Cx.R (c : Cx) (s : State) (j : Nat) (U : List Nat) : List Nat × List Nat :=
  Mdl.blockR Mdl.recI (c.V s) c.vl (c.vl / 2) j U

set_option maxHeartbeats 16000000 in
/-- **after the recursive call** (pure) -/
theorem rec_post {R : RtInv} {c : Cx} {s X X' : State} {Lk : List (Nat × Nat)} {bk j : Nat} {Z U : List Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s)) (hbd : Bd c s X.mem j Z)
    (hbs : Bs c s X.mem j) (hj : c.vl / 2 < j) (hjm : j ≤ c.u1 - c.vl) (huk : Asm.limbs X.mem c.up c.u1 = U)
    (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14)
    (hbud : c.lo s + (j / (c.vl / 2) + 1) * c.K s + stkR c.Hq X.mem c.st ≤ bk)
    (hpost : DrsPostW R bk Lk c.Hq (drsCQ (c.vl + 1) (c.vl - c.vl / 2 + 1)) (c.W - 400) c.t0
      (c.vl / 2 + 1) c.st (c.up + 8 * (j - 1)) (c.vl + 1) (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) X X')
    (hreg : X'.mem.regions = X.mem.regions) :
    ∃ L' b', Ev R c s L' b' X'.mem ∧ Fp R c s L' X'.mem (c.l1 s) ∧ Bd c s X'.mem j Z ∧ Bs c s X'.mem j ∧
      Asm.limbs X'.mem c.t0 (c.vl / 2 + 1) = (c.R s j U).1 ∧
      Asm.limbs X'.mem c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2 ∧
      c.lo s + (j / (c.vl / 2)) * c.K s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq X'.mem c.st ≤ b' := by
  have hW := hcr.hW; have hWg := drsW64_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb0, -, -⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb0
  obtain ⟨-, -, hqh, hqo, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huo, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvo, -, -, -⟩ := hpre.va
  have huv := hpre.uv; have hqu := hpre.qu
  obtain ⟨-, hstw, -, -⟩ := hpre.sti
  have hqs := hpre.sq.1; have hus := hpre.su.1; have hvs := hpre.sv2.1
  obtain ⟨-, -, hq, hr, L', b', ⟨hx, hb', hinv⟩, hsb, hMF, hLF⟩ := hpost
  have hMF' : MemFrame X.mem X'.mem (R.rt ++ win X (c.W - 400) 96 ++ (wsR c j ++ stkWs X.mem c.st)) := by
    rw [← List.append_assoc]; exact hMF
  have hlen := hfp.len
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hev.sok.2.2.2.2.2.1
  have fq := hfp.fq; have fu := hfp.fu; have fv := hfp.fv; have ffw := hfp.fw
  rw [← hlen] at fq fu fv ffw
  have h0 : 408 ≤ (s.regs 4).toNat := by omega
  -- the callee's writes avoid the own slots
  have hws504 : Outside ((s.regs 4).toNat - 408) 504 (wsR c j ++ stkWs X.mem c.st) := by
    have a1 := out504 hcr.t0w (by omega) (by omega)
    have a2 := out504 (huo.of_sub (a := c.up + 8 * (j - 1)) (n := 8 * (c.vl + 1)) (by omega) (by omega)) (by omega) (by omega)
    have a3 := out504 hstw (by omega) (by omega)
    have a4 := out504 ffw (by omega) (by omega)
    simp only [wsR, stkWs, outside_append, outside_cons, outside_nil, and_true] at a1 a2 a3 a4 ⊢
    refine ⟨⟨a1, a2⟩, a3, ?_⟩
    rw [show stW X.mem c.st + 8 * stCap X.mem c.st = stW X.mem c.st + 8 * stLen X.mem c.st +
      8 * (stCap X.mem c.st - stLen X.mem c.st) by omega]; exact a4
  obtain ⟨fo, io, bo⟩ := fo504 hws504 h0
  -- reads kept
  have kp : ∀ {x n : Nat}, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.t0 (8 * (c.vl / 2 + 1)) →
      (x + n ≤ c.up + 8 * (j - 1) ∨ c.up + 8 * (j - 1) + 8 * (c.vl + 1) ≤ x) → Apart x n c.st 24 →
      Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)) →
      X'.mem.readLE x n = X.mem.readLE x n := fun hh hw' h1 h2 h3 h4 =>
    keepP hcr hsp hMF' hLF hh hw' h1 h2 h3 h4 hlc
  have t0q := hcr.t0q; have t0u := hcr.t0u; have t0v := hcr.t0v
  have kv : X'.mem.readLE c.vp (8 * c.vl) = X.mem.readLE c.vp (8 * c.vl) :=
    kp (hext.held hvh) hvo t0v.symm (by unfold Apart at huv; omega) hvs fv.symm
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul →
      (x + n ≤ c.up + 8 * (j - 1) ∨ c.up + 8 * (j - 1) + 8 * (c.vl + 1) ≤ x) →
      X'.mem.readLE x n = X.mem.readLE x n := fun x n h1 h2 h3 =>
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apL t0u.symm h1 h2) h3 (apL hus h1 h2) (apL fu.symm h1 h2)
  have kz : X'.mem.readLE c.qp (8 * c.ql) = X.mem.readLE c.qp (8 * c.ql) :=
    kp (hext.held hqh) hqo t0q.symm (by unfold Apart at hqu; omega) hqs fq.symm
  -- environment
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hS : ∀ x k, Outside x k (win s c.W 96) → Outside x k (win X (c.W - 400) 96) := fun x k ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hsp]; omega
  have hW1 : ∀ x k, Outside x k (R.rt ++ win s c.W 96 ++ c.ws s) → Outside x k (wsR c j) := fun x k ho => by
    have a1 := hloc.1 x k ho
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho a1 ⊢
    exact ⟨a1, by omega⟩
  have hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k (wsR c j) := fun x k hin ho => by
    have a1 := hloc.2 x k hin ho
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho a1 ⊢
    exact ⟨a1, by omega⟩
  have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' X'.mem := Ev.callS hcr hev hl hMF hLF hS hW1 hW2 hx (by rw [← h14]; exact hinv) hsb hreg
  have hFp : Fp R c s L' X'.mem (c.l1 s) :=
    Fp.callS hcr hev hfp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  have hBd : Bd c s X'.mem j Z := hbd.frame hMF'
    (fixOut_callee hout (by omega) (by omega) hsp (by omega) fo)
    (iOut_callee hout (by omega) (by omega) hsp (by omega) io) kv
    (ku _ _ (by omega) (by omega) (Or.inr (by omega))) kz
  have hBs : Bs c s X'.mem j := hbs.frame hMF' (bOut_callee hout (by omega) (by omega) hsp (by omega) bo)
  -- values
  have hv0 : X.mem.readLE (c.vp + 8 * (c.vl / 2 - 1)) (8 * (c.vl - c.vl / 2 + 1)) =
      s.mem.readLE (c.vp + 8 * (c.vl / 2 - 1)) (8 * (c.vl - c.vl / 2 + 1)) :=
    rd_sub hbd.vk (by omega) (by omega)
  obtain ⟨e1, e2⟩ := rec_val (M0 := s.mem) h40 hj (by omega) huk hv0 hq hr
  refine ⟨L', b', hEv, hFp, hBd, hBs, e1, ?_, ?_⟩
  · rw [Asm.limbs_upd (j := j - 1) (k := c.vl + 1) (by omega) (fun i hi hi2 => ku _ _ (by omega) (by omega)
      (by omega)), huk, e2]
  · have hc : drsCQ (c.vl + 1) (c.vl - c.vl / 2 + 1) ≤ drsCQ c.ul (c.vl - c.vl / 2 + 1) :=
      drsCQ_ul64 _ _ _ (by omega)
    have e : (j / (c.vl / 2) + 1) * c.K s = j / (c.vl / 2) * c.K s + c.K s := Nat.succ_mul _ _
    simp only [Cx.K] at e hbud ⊢
    omega

/-- the return address of the recursive call of the loop body (`CALL 0x5efc2c`) -/
abbrev r2 : Nat := 0x5efc31

/-- **after the recursive call** (iteration `j`; `Z`/`U` = quotient/dividend at the iteration start) -/
structure A2 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 r2
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  bd : Bd c s S.mem j Z
  bs : Bs c s S.mem j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  qk : Asm.limbs S.mem c.t0 (c.vl / 2 + 1) = (c.R s j U).1
  uk : Asm.limbs S.mem c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq S.mem c.st ≤ bk

end FvModexp.Amd64.Q.DivRec
