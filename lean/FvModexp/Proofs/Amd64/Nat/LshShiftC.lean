import FvModexp.Proofs.Amd64.Nat.LshFin
import FvModexp.Proofs.Amd64.Nat.Callees2
import FvModexp.Proofs.Common.SetBytesMath

/-!
# `nat.lsh` (amd64): shift path from `CALL lshVU.abi0` (`+0x28d`) to the clear point

At the call: frame words `0 … 0x30(RSP') = e - 144 … e - 96` = `(p + 8 (s/64), m, c - s/64, x, m, cap x, s % 64)`,
spills `e - 24 = p`, `e - 80 = c`. After the call: `XORPS X15, X15; MOVQ FS:-8, R14`; `AX = [e-56]`, `CX = [e-48]`;
`CMPQ AX, CX; JBE panic`; `z[n] = [e-88]` (the carry); `AX = p`, `CX = [e-80]`, `DX = [e-56]`, `BX = [e-40]`; to `hClr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Lsh

theorem carry_lt (X r n : Nat) (hX : X < 2 ^ (64 * n)) (hr : r < 64) : X * 2 ^ r / 2 ^ (64 * n) < 2 ^ 64 := by
  apply Nat.div_lt_of_lt_mul
  calc X * 2 ^ r < 2 ^ (64 * n) * 2 ^ r := Nat.mul_lt_mul_of_pos_right hX (Nat.two_pow_pos _)
    _ ≤ 2 ^ (64 * n) * 2 ^ 64 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- `lshVU`'s postcondition with the frame words of the call state known -/
theorem lshQ {C : State} {m : Janus.Arm64.Memory} {z n x r : Nat}
    (hz : C.mem.readLE ((C.regs 4).toNat + 8) 8 = z)
    (hn : C.mem.readLE ((C.regs 4).toNat + 16) 8 = n) (hx : C.mem.readLE ((C.regs 4).toNat + 32) 8 = x)
    (hs : C.mem.readLE ((C.regs 4).toNat + 56) 8 = r) (h : LshVUSum.Q C m) :
    natVal m z n = (natVal C.mem x n * 2 ^ r) % 2 ^ (64 * n) ∧
      m.readLE ((C.regs 4).toNat + 64) 8 = (natVal C.mem x n * 2 ^ r) / 2 ^ (64 * n) ∧
      MemFrame C.mem m [(z, z + 8 * n), ((C.regs 4).toNat + 64, (C.regs 4).toNat + 72)] := by
  unfold LshVUSum.Q at h
  rw [hz, hn, hx, hs] at h
  exact h

set_option maxRecDepth 20000 in
/-- memory facts after `lshVU` and `z[n] = carry` (pure); `C` = the memory at the call (before the push) -/
theorem shift_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M C w : Janus.Arm64.Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M C [((s.regs 4).toNat - 152, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72),
      ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)])
    (hQ1 : natVal w (p + 8 * (sh / 64)) xl = natVal C x xl * 2 ^ (sh % 64) % 2 ^ (64 * xl))
    (hQ3 : MemFrame C w [(p + 8 * (sh / 64), p + 8 * (sh / 64) + 8 * xl), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 80)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' w)) :
    MemFrame M (w.writeLE (p + (xl + sh / 64) * 8) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl)))
      (R.rt ++ ws s p c) ∧
    LiveFrame M (w.writeLE (p + (xl + sh / 64) * 8) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl))) L'
      [(p, p + 8 * c)] ∧
    R.inv b' L' (s.regs 14).toNat
      (view R.rt L' (w.writeLE (p + (xl + sh / 64) * 8) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl)))) ∧
    natVal (w.writeLE (p + (xl + sh / 64) * 8) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl)))
      (p + 8 * (sh / 64)) (xl + 1) = natVal s.mem x xl * 2 ^ (sh % 64) := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt
  simp only [need] at hcap
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hS : MemFrame w (w.writeLE (p + (xl + sh / 64) * 8) 8 (natVal C x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl)))
      [(p + (xl + sh / 64) * 8, p + (xl + sh / 64) * 8 + 8)] := by
    janus_frame
  have hA : MemFrame M w (R.rt ++ ws s p c) := hF.trans hQ3 fun a k ho => by
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩
  have hxC : natVal C x xl = natVal s.mem x xl := by
    simp only [natVal]
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact h.xr _ _ (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨hA.trans hS fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hS.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ3.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · exact inv_store_held hinv (h.pheld.sub (by omega) (by omega))
  · rw [show p + (xl + sh / 64) * 8 = p + 8 * (sh / 64) + 8 * xl by omega,
      natVal_store_top _ _ _ _ (carry_lt _ _ _ (natVal_lt _ _ _) (Nat.mod_lt _ (by decide))), hQ1, hxC,
      Nat.mod_add_div]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `lshVU` (return state `T`, memory `w`): `XORPS`, `R14` reload, reloads, `z[n] = carry`, to `hClr` -/
theorem shiftT (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (w : Janus.Arm64.Memory) (cy : Nat)
    (hF1 : MemFrame M (w.writeLE (p + (xl + sh / 64) * 8) 8 cy) (R.rt ++ ws s p c))
    (hLF1 : LiveFrame M (w.writeLE (p + (xl + sh / 64) * 8) 8 cy) L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' (w.writeLE (p + (xl + sh / 64) * 8) 8 cy)))
    (hval : natVal (w.writeLE (p + (xl + sh / 64) * 8) 8 cy) (p + 8 * (sh / 64)) (xl + 1) =
      natVal s.mem x xl * 2 ^ (sh % 64))
    (w5 : w.readLE ((s.regs 4).toNat - 24) 8 = p) (w6 : w.readLE ((s.regs 4).toNat - 80) 8 = c)
    (w7 : w.readLE ((s.regs 4).toNat - 40) 8 = sh / 64) (w8 : w.readLE ((s.regs 4).toNat - 48) 8 = xl + sh / 64)
    (w9 : w.readLE ((s.regs 4).toNat - 56) 8 = xl + sh / 64 + 1) (wc : w.readLE ((s.regs 4).toNat - 88) 8 = cy)
    (wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat)
    (wtacc : w.accessible (s.fsBase.toNat - 8) 8 false = true)
    (hwacc : w.accessible (p + (xl + sh / 64) * 8) 8 true = true)
    (hsacc : w.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (callLsh + 5)) (hsp : T.regs 4 = s.regs 4 - 144#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (hfs : T.fsBase = s.fsBase) (hdf : T.df = false) (hm : T.mem = w) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) T fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hal := h.al; have hpw := h.pw; have htw := h.tw
  simp only [need] at hcap hn16
  unfold Apart at hpw htw
  have htb := h.tlsg.base
  janus64_run [hm, w5, w6, w7, w8, w9, wc, wtl, hfs, BitVec.msb_eq_decide] until [hClr]
  refine fromClr impl R hmc b L zp zc x xl sh s p c L' b' M h _ hF1 hLF1 hinv2 hval ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := w) _ (by omega)).trans w5
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := w) _ (by omega)).trans w9
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := w) _ (by omega)).trans w6
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf | exact h.x15.symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `CALL lshVU.abi0` (state `C`) to the clear point, then `fromClr` -/
theorem shiftC (impl : List Amd64.Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0)
    (C : State) (hpc : C.rip = BitVec.ofNat 64 callLsh) (hsp : C.regs 4 = s.regs 4 - 144#64)
    (h5 : C.regs 5 = s.regs 4 - 8#64) (h14 : C.regs 14 = s.regs 14) (hx15 : C.xmm 15 = s.xmm 15)
    (hfs : C.fsBase = s.fsBase) (hdf : C.df = false)
    (hF : MemFrame M C.mem [((s.regs 4).toNat - 144, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72),
      ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)])
    (k1 : C.mem.readLE ((s.regs 4).toNat - 152 + 8) 8 = p + 8 * (sh / 64))
    (k2 : C.mem.readLE ((s.regs 4).toNat - 152 + 16) 8 = xl)
    (k3 : C.mem.readLE ((s.regs 4).toNat - 152 + 32) 8 = x)
    (k4 : C.mem.readLE ((s.regs 4).toNat - 152 + 56) 8 = sh % 64)
    (k5 : C.mem.readLE ((s.regs 4).toNat - 24) 8 = p) (k6 : C.mem.readLE ((s.regs 4).toNat - 80) 8 = c)
    (hinvC : R.inv b' L' (s.regs 14).toNat (view R.rt L' C.mem)) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) C fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hxl0 := h.xl0; have hal := h.al; have hx48 := h.x48
  have hwrt := h.wrt; have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpf := h.pf; have htw := h.tw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  simp only [need] at hcap hn16
  unfold Apart at hpw hgw hpg hpf htw
  have rC : ∀ a, ((s.regs 4).toNat - 72 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 24) ∨
      ((s.regs 4).toNat - 16 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → C.mem.readLE a 8 = M.readLE a 8 := fun a ha =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have k7 : C.mem.readLE ((s.regs 4).toNat - 40) 8 = sh / 64 := (rC _ (by omega)).trans h.sq
  have k8 : C.mem.readLE ((s.regs 4).toNat - 48) 8 = xl + sh / 64 := (rC _ (by omega)).trans h.sn
  have k9 : C.mem.readLE ((s.regs 4).toNat - 56) 8 = xl + sh / 64 + 1 := by
    rw [rC _ (by omega)]; have := h.sn1; simp only [need] at this; exact this
  have hCacc : ∀ a n v, C.mem.accessible a n v = M.accessible a n v := fun a n v => by rw [hF.accessible]
  have hzacc : C.mem.accessible (p + 8 * (sh / 64)) (8 * xl) true = true := by
    rw [hCacc]; exact Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hzacc' := Janus.Arm64.Memory.accessible_weaken _ hzacc
  have hxacc : C.mem.accessible x (8 * xl) false = true := by rw [hCacc]; exact h.xacc
  have hwacc : C.mem.accessible ((s.regs 4).toNat - 152) 72 true = true := by
    rw [hCacc]; exact Janus.Arm64.Memory.accessible_mono _ h.sacc (by omega) (by omega)
  have hzH : Held R L' (p + 8 * (sh / 64)) (8 * xl) := h.pheld.sub (by omega) (by omega)
  have hro : Outside ((s.regs 4).toNat - 152 + 64) 8 R.rt := hwrt.of_sub (by omega) (by omega)
  have hzg : Apart (p + 8 * (sh / 64)) (8 * xl) ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hzt : Apart (p + 8 * (sh / 64)) (8 * xl) (s.fsBase.toNat - 8) 8 := by unfold Apart; omega
  have hrg : Apart ((s.regs 4).toNat - 152 + 64) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hrt : Apart ((s.regs 4).toNat - 152 + 64) 8 (s.fsBase.toNat - 8) 8 := by unfold Apart; omega
  have hzr : Apart (p + 8 * (sh / 64)) (8 * xl) ((s.regs 4).toNat - 152) 72 := by unfold Apart; omega
  have hxr : Apart x (8 * xl) ((s.regs 4).toNat - 152 + 64) 8 := by unfold Apart; omega
  have halx : x ≤ p + 8 * (sh / 64) ∨ Apart (p + 8 * (sh / 64)) (8 * xl) x (8 * xl) := by
    rcases h.px with e | e
    · left; omega
    · right; unfold Apart at e ⊢; omega
  have hr1 : 1 ≤ sh % 64 := Nat.pos_of_ne_zero hr0
  have hr63 : sh % 64 ≤ 63 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have hra : (6187186 : Nat) < 2 ^ 47 := by decide
  janus64_run [k1, k2, k3, k4, hfs] until [callLsh + 5] calls [hLsh b' L']
  rename_i w _ _ hq hinvw hgd htl
  have e152 : (s.regs 4 - 152#64).toNat = (s.regs 4).toNat - 152 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have kk : ∀ k v, (s.regs 4).toNat - 152 + 8 ≤ k → C.mem.readLE k 8 = v →
      (C.mem.writeLE ((s.regs 4).toNat - 152) 8 6187186).readLE k 8 = v := fun k v hk h => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h
  obtain ⟨q1, q2, q3⟩ := lshQ (z := p + 8 * (sh / 64)) (n := xl) (x := x) (r := sh % 64)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k1)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k2)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k3)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k4) hq
  simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152,
    show (s.regs 4).toNat - 152 + 64 = (s.regs 4).toNat - 88 by omega,
    show (s.regs 4).toNat - 152 + 72 = (s.regs 4).toNat - 80 by omega] at q1 q2 q3
  have hP : MemFrame M (C.mem.writeLE ((s.regs 4).toNat - 152) 8 6187186)
      [((s.regs 4).toNat - 152, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72),
        ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)],
     fun a n v => by rw [Janus.Arm64.Memory.accessible_writeLE, hF.accessible]⟩
  obtain ⟨hF1, hLF1, hinv2, hval⟩ := shift_facts h hP q1 q3 hinvw
  have rw' : ∀ a, ((s.regs 4).toNat - 80 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) →
      w.readLE a 8 = C.mem.readLE a 8 := fun a ha => by
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact kk _ _ (by omega) rfl
  have w5 := (rw' _ (by omega)).trans k5
  have w6 := (rw' _ (by omega)).trans k6
  have w7 := (rw' _ (by omega)).trans k7
  have w8 := (rw' _ (by omega)).trans k8
  have w9 := (rw' _ (by omega)).trans k9
  have wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    have := h.tls; have := h.trt
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hP.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.tls
  have wtacc : w.accessible (s.fsBase.toNat - 8) 8 false = true := by
    rw [q3.accessible, hP.accessible]; exact h.tacc
  have hwacc : w.accessible (p + (xl + sh / 64) * 8) 8 true = true := by
    rw [q3.accessible, hP.accessible]; exact Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hsacc' : w.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true := by
    rw [q3.accessible, hP.accessible]; exact h.sacc
  refine shiftT impl R hmc b L zp zc x xl sh s p c L' b' M h w _ hF1 hLF1 hinv2 hval w5 w6 w7 w8 w9 q2 wtl wtacc
    hwacc hsacc' _ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf

end FvModexp.Amd64.Lsh
