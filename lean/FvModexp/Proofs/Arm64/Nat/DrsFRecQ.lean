import FvModexp.Proofs.Arm64.Nat.DrsFRel
import FvModexp.Proofs.Arm64.Nat.WinIn

/-!
# `divRecursiveStep` (arm64), final block: after the recursive call (pure)

`rec_valF` (the lists: `qhat0` = `(Cx.RF …).1`, `u[s:s+k]` = `(Cx.RF …).2`, with `k` = `len(u[s:].norm())`) and
`rec_postF` (`Ev`/`Fp`/`BdF`, the lists and the budget after the call). Adapted from `rec_val`/`rec_post` (DrsRecQ/DrsA2).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the writes of the final block's recursive call (its `z` = `qhat0` and `u = u[s:s+k]`) -/
@[reducible] def wsRF (c : Cx) (k : Nat) : List (Nat × Nat) :=
  [(c.t0, c.t0 + 8 * (c.vl / 2 + 1)), (c.up + 8 * (c.vl / 2 - 1), c.up + 8 * (c.vl / 2 - 1) + 8 * k)]

/-- **the lists after the final block's recursive call** -/
theorem rec_valF {M0 M M' : Memory} {up u1 vp n t0 k : Nat} {U : List Nat} (h40 : 40 ≤ n) (hnu : n ≤ u1)
    (huk : Asm.limbs M up u1 = U) (hk : k ≤ u1 - (n / 2 - 1))
    (hkv : natVal M (up + 8 * (n / 2 - 1)) k = natVal M (up + 8 * (n / 2 - 1)) (u1 - (n / 2 - 1)))
    (hkN : NatNorm M (up + 8 * (n / 2 - 1)) k)
    (hv : M.readLE (vp + 8 * (n / 2 - 1)) (8 * (n - n / 2 + 1)) = M0.readLE (vp + 8 * (n / 2 - 1)) (8 * (n - n / 2 + 1)))
    (hq : natVal M' t0 (n / 2 + 1) =
      natVal M (up + 8 * (n / 2 - 1)) k / natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1))
    (hr : natVal M' (up + 8 * (n / 2 - 1)) k =
      natVal M (up + 8 * (n / 2 - 1)) k % natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1)) :
    Asm.limbs M' t0 (n / 2 + 1) = (Mdl.finR Mdl.recI (Asm.limbs M0 vp n) (n / 2) U).1 ∧
      Asm.limbs M' (up + 8 * (n / 2 - 1)) k = (Mdl.finR Mdl.recI (Asm.limbs M0 vp n) (n / 2) U).2 := by
  have e0 : U.drop (n / 2 - 1) = Asm.limbs M (up + 8 * (n / 2 - 1)) (u1 - (n / 2 - 1)) := by
    rw [← huk]; exact drop_limbs_v (by omega)
  have e1 : Mdl.norm (U.drop (n / 2 - 1)) = Asm.limbs M (up + 8 * (n / 2 - 1)) k :=
    (Asm.limbs_norm e0.symm hkv hkN).symm
  have e2 : (Asm.limbs M0 vp n).drop (n / 2 - 1) = Asm.limbs M0 (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1) := by
    rw [drop_limbs_v (by omega), show n - (n / 2 - 1) = n - n / 2 + 1 by omega]
  have ev : Mdl.val (Asm.limbs M0 (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1)) =
      natVal M (vp + 8 * (n / 2 - 1)) (n - n / 2 + 1) := by
    rw [Asm.val_limbs]; show M0.readLE _ _ = M.readLE _ _; exact hv.symm
  unfold Mdl.finR Mdl.recI
  rw [e1, e2, Asm.val_limbs, ev]
  simp only [List.length_replicate, Asm.length_limbs]
  refine ⟨?_, ?_⟩
  · rw [Mdl.eq_toL (Asm.Wd_limbs M' t0 (n / 2 + 1)), Asm.val_limbs, Asm.length_limbs]
    exact congrArg (Mdl.toL · (n / 2 + 1)) hq
  · rw [Mdl.eq_toL (Asm.Wd_limbs M' _ k), Asm.val_limbs, Asm.length_limbs]
    exact congrArg (Mdl.toL · k) hr

/-- a range apart from the recursive call's writes keeps its bytes -/
theorem keepPF {R : RtInv} {c : Cx} {s X X' : State} {Lk : List (Nat × Nat)} {k x n : Nat}
    (hcr : Cr R c s) (hsp : X.sp.toNat = s.sp.toNat - 400)
    (hF : MemFrame X.mem X'.mem (R.rt ++ winA X (c.W - 400) 96 ++ (wsRF c k ++ stkWs X.mem c.st)))
    (hL : LiveFrame X.mem X'.mem Lk (wsRF c k ++ stkWs X.mem c.st)) (hh : Held R Lk x n)
    (hw : Outside x n (win s c.W 96)) (h1 : Apart x n c.t0 (8 * (c.vl / 2 + 1)))
    (h2 : x + n ≤ c.up + 8 * (c.vl / 2 - 1) ∨ c.up + 8 * (c.vl / 2 - 1) + 8 * k ≤ x) (h3 : Apart x n c.st 24)
    (h4 : Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)))
    (hlc : stLen X.mem c.st ≤ stCap X.mem c.st) :
    X'.mem.readLE x n = X.mem.readLE x n := by
  have hW := hcr.hW; have := drsW_ge c.vl
  refine keepRd hcr hsp (by omega) (by omega) hF hL hh hw ?_
  unfold Apart at h1 h3 h4
  simp only [wsRF, stkWs, outside_append, outside_cons, outside_nil, and_true]
  omega

set_option maxHeartbeats 16000000 in
/-- **after the recursive call** (pure) -/
theorem rec_postF {R : RtInv} {c : Cx} {s X X' : State} {Lk : List (Nat × Nat)} {bk k : Nat} {Z U : List Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s)) (hbd : BdF c s X.mem Z)
    (hk : k ≤ c.u1 - (c.vl / 2 - 1)) (huk : Asm.limbs X.mem c.up c.u1 = U)
    (hkv : natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) k = natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)))
    (hkN : NatNorm X.mem (c.up + 8 * (c.vl / 2 - 1)) k)
    (hsp : X.sp.toNat = s.sp.toNat - 400) (h28 : X.regs 28 = s.regs 28) (hbud : c.lo s + c.K s ≤ bk)
    (hpost : DrsPostW R bk Lk (drsC (stLen X.mem c.st) k (c.vl - c.vl / 2 + 1)) (c.W - 400) c.t0
      (c.vl / 2 + 1) c.st (c.up + 8 * (c.vl / 2 - 1)) k (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) X X')
    (hreg : X'.mem.regions = X.mem.regions) :
    ∃ L' b', Ev R c s L' b' X'.mem ∧ Fp R c s L' X'.mem (c.l1 s) ∧ BdF c s X'.mem Z ∧
      Asm.limbs X'.mem c.t0 (c.vl / 2 + 1) = (c.RF s U).1 ∧
      Asm.limbs X'.mem c.up c.u1 = c.UF s U ∧
      c.lo s + stackNatCost (c.l1 s) (3 * c.vl) +
        mulC (c.l1 s + StackNat.rnd (3 * c.vl)) (c.vl / 2 + 1) (c.vl / 2 - 1) ≤ b' := by
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, hqh, hqo, -⟩, ⟨-, -, huh, huo, -⟩, ⟨-, -, hvh, hvo, -, -, -⟩, -, -, huv,
    ⟨-, hstw, -, -⟩, -, ⟨hqs, -⟩, ⟨hus, -⟩, ⟨hvs, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨hq, hr, L', b', ⟨hx, hb', hinv⟩, hsb, hMF, hLF⟩ := hpost
  have hMF' : MemFrame X.mem X'.mem (R.rt ++ winA X (c.W - 400) 96 ++ (wsRF c k ++ stkWs X.mem c.st)) := by
    rw [← List.append_assoc]; exact hMF
  have hlen := hfp.len
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hev.sok.2.2.2.2.2.1
  have fq := hfp.fq; have fu := hfp.fu; have fv := hfp.fv; have ffw := hfp.fw
  rw [← hlen] at fq fu fv ffw
  have h0 : 408 ≤ s.sp.toNat := by omega
  -- the callee's writes avoid the own slots
  have hws504 : Outside (s.sp.toNat - 408) 504 (wsRF c k ++ stkWs X.mem c.st) := by
    have a1 := out504 hcr.t0w (by omega) (by omega)
    have a2 := out504 (huo.of_sub (a := c.up + 8 * (c.vl / 2 - 1)) (n := 8 * k) (by omega) (by omega)) (by omega) (by omega)
    have a3 := out504 hstw (by omega) (by omega)
    have a4 := out504 ffw (by omega) (by omega)
    simp only [wsRF, stkWs, outside_append, outside_cons, outside_nil, and_true] at a1 a2 a3 a4 ⊢
    refine ⟨⟨a1, a2⟩, a3, ?_⟩
    rw [show stW X.mem c.st + 8 * stCap X.mem c.st = stW X.mem c.st + 8 * stLen X.mem c.st +
      8 * (stCap X.mem c.st - stLen X.mem c.st) by omega]; exact a4
  obtain ⟨fo, -, -⟩ := fo504 hws504 h0
  have ffo := fo504F hws504 h0
  -- reads kept
  have kp : ∀ {x n : Nat}, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.t0 (8 * (c.vl / 2 + 1)) →
      (x + n ≤ c.up + 8 * (c.vl / 2 - 1) ∨ c.up + 8 * (c.vl / 2 - 1) + 8 * k ≤ x) → Apart x n c.st 24 →
      Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)) →
      X'.mem.readLE x n = X.mem.readLE x n := fun hh hw' h1 h2 h3 h4 =>
    keepPF hcr hsp hMF' hLF hh hw' h1 h2 h3 h4 hlc
  have t0q := hcr.t0q; have t0u := hcr.t0u; have t0v := hcr.t0v
  have kv : X'.mem.readLE c.vp (8 * c.vl) = X.mem.readLE c.vp (8 * c.vl) :=
    kp (hext.held hvh) hvo t0v.symm (by unfold Apart at huv; omega) hvs fv.symm
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul →
      (x + n ≤ c.up + 8 * (c.vl / 2 - 1) ∨ c.up + 8 * (c.vl / 2 - 1) + 8 * k ≤ x) →
      X'.mem.readLE x n = X.mem.readLE x n := fun x n h1 h2 h3 =>
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apS t0u.symm h1 h2) h3 (apS hus h1 h2) (apS fu.symm h1 h2)
  have kz : X'.mem.readLE c.qp (8 * c.ql) = X.mem.readLE c.qp (8 * c.ql) :=
    kp (hext.held hqh) hqo t0q.symm (by
      have := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; unfold Apart at this; omega) hqs fq.symm
  -- environment
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hS : ∀ x m, Outside x m (winA s c.W 96) → Outside x m (winA X (c.W - 400) 96) := fun _ _ ho =>
    winA_in ho hsp (by omega) (by omega) (by omega)
  have hW1 : ∀ x m, Outside x m (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x m (wsRF c k) := fun x m ho => by
    have a1 := hloc.1 x m ho
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho a1 ⊢
    exact ⟨a1, by omega⟩
  have hW2 : ∀ x m, InRanges x m c.L → Outside x m (c.ws s) → Outside x m (wsRF c k) := fun x m hin ho => by
    have a1 := hloc.2 x m hin ho
    simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho a1 ⊢
    exact ⟨a1, by omega⟩
  have hl : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hlen]; simp only [Cx.l1]; omega
  have hEv : Ev R c s L' b' X'.mem := Ev.callS hcr hev hl hMF hLF hS hW1 hW2 hx (by rw [← h28]; exact hinv) hsb hreg
  have hFp : Fp R c s L' X'.mem (c.l1 s) :=
    Fp.callS hcr hev hfp (by simp only [Cx.l1, StackNat.rnd]; omega) hx hsb
  have hBd : BdF c s X'.mem Z := hbd.frame hMF'
    (fixOut_callee hout (by omega) (by omega) hsp (by omega) fo)
    (fOut_callee hout (by omega) (by omega) hsp (by omega) ffo) kv
    (ku _ _ (by omega) (by omega) (Or.inr (by omega))) kz
  -- values
  have hv0 : X.mem.readLE (c.vp + 8 * (c.vl / 2 - 1)) (8 * (c.vl - c.vl / 2 + 1)) =
      s.mem.readLE (c.vp + 8 * (c.vl / 2 - 1)) (8 * (c.vl - c.vl / 2 + 1)) :=
    rd_sub hbd.vk (by omega) (by omega)
  obtain ⟨e1, e2⟩ := rec_valF (M0 := s.mem) h40 (by omega) huk hk hkv hkN hv0 hq hr
  refine ⟨L', b', hEv, hFp, hBd, e1, ?_, ?_⟩
  · rw [Asm.limbs_upd (j := c.vl / 2 - 1) (k := k) (by omega) (fun i hi hi2 => ku _ _ (by omega) (by omega)
      (by omega)), huk, e2]
  · have hc : drsC (stLen X.mem c.st) k (c.vl - c.vl / 2 + 1) ≤ drsC (c.l1 s) c.ul (c.vl - c.vl / 2 + 1) := by
      rw [hlen]; exact drsC_ul _ _ _ _ (by omega)
    simp only [Cx.K] at hbud ⊢
    omega

end FvModexp.Arm64.DivRec
