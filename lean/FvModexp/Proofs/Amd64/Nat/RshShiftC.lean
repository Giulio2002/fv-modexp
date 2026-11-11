import FvModexp.Proofs.Amd64.Nat.RshFin
import FvModexp.Proofs.Amd64.Nat.RshCallee

/-!
# `nat.rsh` (amd64): shift path from `CALL rshVU.abi0` (`+0x2ac`) to the norm head

At the call: frame words `0 … 0x30(RSP') = e - 144 … e - 96` = `(p, n, c, x + 8q, n, cap x - q, s % 64)`
(`q = s / 64`), spills `e - 72 = c`, `e - 80 = n`, `e - 24 = p`. After the call: `XORPS X15, X15; MOVQ FS:-8, R14`;
`AX = [e-24]`, `CX = [e-72]`, `DI = [e-80]`; to `hNorm`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

/-- `rshVU`'s postcondition with the frame words of the call state known -/
theorem rshQ {C : State} {m : Janus.Arm64.Memory} {z n x r : Nat}
    (hz : C.mem.readLE ((C.regs 4).toNat + 8) 8 = z)
    (hn : C.mem.readLE ((C.regs 4).toNat + 16) 8 = n) (hx : C.mem.readLE ((C.regs 4).toNat + 32) 8 = x)
    (hs : C.mem.readLE ((C.regs 4).toNat + 56) 8 = r) (h : RshVUSum.Q C m) :
    natVal m z n = natVal C.mem x n / 2 ^ r ∧
      MemFrame C.mem m [(z, z + 8 * n), ((C.regs 4).toNat + 64, (C.regs 4).toNat + 72)] := by
  unfold RshVUSum.Q at h
  rw [hz, hn, hx, hs] at h
  exact ⟨h.1, h.2.2⟩

set_option maxRecDepth 20000 in
/-- memory facts after `rshVU` (pure); `C` = the memory at the call with the return-address push -/
theorem shift_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M C w : Janus.Arm64.Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M C [((s.regs 4).toNat - 152, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)])
    (hQ1 : natVal w p (need xl sh) = natVal C (x + 8 * (sh / 64)) (need xl sh) / 2 ^ (sh % 64))
    (hQ3 : MemFrame C w [(p, p + 8 * need xl sh), ((s.regs 4).toNat - 88, (s.regs 4).toNat - 80)]) :
    MemFrame M w (R.rt ++ ws s p c) ∧ LiveFrame M w L' [(p, p + 8 * c)] ∧
    natVal w p (need xl sh) = natVal s.mem x xl / 2 ^ sh := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hpx := h.px; have hn0 := h.n0; have hx48 := h.x48
  simp only [need] at hcap hn0 hQ1 hQ3 ⊢
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hpx
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  refine ⟨hF.trans hQ3 fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hQ3.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · have hxC : natVal C (x + 8 * (sh / 64)) (xl - sh / 64) = natVal s.mem x xl / 2 ^ (64 * (sh / 64)) := by
      rw [val_hi, show sh / 64 + (xl - sh / 64) = xl by omega]
      simp only [natVal]
      rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      rw [h.xr _ _ (Nat.le_refl _) (Nat.le_refl _)]
    rw [hQ1, hxC, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * (sh / 64) + sh % 64 = sh by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `rshVU` (return state `T`, memory `w`): `XORPS`, `R14` reload, reloads, to `hNorm` -/
theorem shiftT (impl : List Amd64.Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (w : Janus.Arm64.Memory)
    (hF1 : MemFrame M w (R.rt ++ ws s p c)) (hLF1 : LiveFrame M w L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' w))
    (hval : natVal w p (need xl sh) = natVal s.mem x xl / 2 ^ sh)
    (w5 : w.readLE ((s.regs 4).toNat - 24) 8 = p) (w6 : w.readLE ((s.regs 4).toNat - 72) 8 = c)
    (w7 : w.readLE ((s.regs 4).toNat - 80) 8 = need xl sh)
    (wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat)
    (wtacc : w.accessible (s.fsBase.toNat - 8) 8 false = true)
    (hsacc : w.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (callRsh + 5)) (hsp : T.regs 4 = s.regs 4 - 144#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (hfs : T.fsBase = s.fsBase) (hdf : T.df = false) (hm : T.mem = w) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) T fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hal := h.al; have htw := h.tw
  unfold Apart at htw
  have htb := h.tlsg.base
  janus64_run [hm, w5, w6, w7, wtl, hfs, BitVec.msb_eq_decide] until [hNorm]
  refine fromNorm impl b R L zp zc x xl sh s p c L' b' M h _ hF1 hLF1 hinv2 hval _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf | exact h.x15.symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `CALL rshVU.abi0` (state `C`) to the norm head, then `fromNorm` -/
theorem shiftC (impl : List Amd64.Segment) (R : RtInv)
    (hRsh : ∀ b L, Summary0 (LibRsh.program.link impl) (segAddr Extracted.program rshVUfn) (RshLPre R b L)
      (RshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0)
    (C : State) (hpc : C.rip = BitVec.ofNat 64 callRsh) (hsp : C.regs 4 = s.regs 4 - 144#64)
    (h5 : C.regs 5 = s.regs 4 - 8#64) (h14 : C.regs 14 = s.regs 14) (hx15 : C.xmm 15 = s.xmm 15)
    (hfs : C.fsBase = s.fsBase) (hdf : C.df = false)
    (hF : MemFrame M C.mem [((s.regs 4).toNat - 144, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)])
    (k1 : C.mem.readLE ((s.regs 4).toNat - 152 + 8) 8 = p)
    (k2 : C.mem.readLE ((s.regs 4).toNat - 152 + 16) 8 = need xl sh)
    (k3 : C.mem.readLE ((s.regs 4).toNat - 152 + 32) 8 = x + 8 * (sh / 64))
    (k4 : C.mem.readLE ((s.regs 4).toNat - 152 + 56) 8 = sh % 64)
    (k5 : C.mem.readLE ((s.regs 4).toNat - 24) 8 = p) (k6 : C.mem.readLE ((s.regs 4).toNat - 72) 8 = c)
    (k7 : C.mem.readLE ((s.regs 4).toNat - 80) 8 = need xl sh)
    (hinvC : R.inv b' L' (s.regs 14).toNat (view R.rt L' C.mem)) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) C fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn0 := h.n0; have hal := h.al; have hx48 := h.x48
  have hwrt := h.wrt; have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpf := h.pf; have htw := h.tw
  have hxw := h.xw; have hpx := h.px
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  simp only [need] at hcap hn0 k2 k7 ⊢
  unfold Apart at hpw hgw hpg hpf htw hpx
  have hCacc : ∀ a n v, C.mem.accessible a n v = M.accessible a n v := fun a n v => by rw [hF.accessible]
  have hzacc : C.mem.accessible p (8 * (xl - sh / 64)) true = true := by
    rw [hCacc]; exact Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : C.mem.accessible (x + 8 * (sh / 64)) (8 * (xl - sh / 64)) false = true := by
    rw [hCacc]; exact Janus.Arm64.Memory.accessible_mono _ h.xacc (by omega) (by omega)
  have hwacc : C.mem.accessible ((s.regs 4).toNat - 152) 72 true = true := by
    rw [hCacc]; exact Janus.Arm64.Memory.accessible_mono _ h.sacc (by omega) (by omega)
  have hzH : Held R L' p (8 * (xl - sh / 64)) := h.pheld.sub (by omega) (by omega)
  have hro : Outside ((s.regs 4).toNat - 152 + 64) 8 R.rt := hwrt.of_sub (by omega) (by omega)
  have hzg : Apart p (8 * (xl - sh / 64)) ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hzt : Apart p (8 * (xl - sh / 64)) (s.fsBase.toNat - 8) 8 := by unfold Apart; omega
  have hrg : Apart ((s.regs 4).toNat - 152 + 64) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hrt : Apart ((s.regs 4).toNat - 152 + 64) 8 (s.fsBase.toNat - 8) 8 := by unfold Apart; omega
  have hzr : Apart p (8 * (xl - sh / 64)) ((s.regs 4).toNat - 152) 72 := by unfold Apart; omega
  have hxr : Apart (x + 8 * (sh / 64)) (8 * (xl - sh / 64)) ((s.regs 4).toNat - 152 + 64) 8 := by unfold Apart; omega
  have halx : p ≤ x + 8 * (sh / 64) ∨ Apart p (8 * (xl - sh / 64)) (x + 8 * (sh / 64)) (8 * (xl - sh / 64)) := by
    right; unfold Apart; omega
  have hr1 : 1 ≤ sh % 64 := Nat.pos_of_ne_zero hr0
  have hr63 : sh % 64 ≤ 63 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have hra : (6188145 : Nat) < 2 ^ 47 := by decide
  janus64_run [k1, k2, k3, k4, hfs] until [callRsh + 5] calls [hRsh b' L']
  rename_i w _ _ hq hinvw hgd htl
  have e152 : (s.regs 4 - 152#64).toNat = (s.regs 4).toNat - 152 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have kk : ∀ k v, (s.regs 4).toNat - 152 + 8 ≤ k → C.mem.readLE k 8 = v →
      (C.mem.writeLE ((s.regs 4).toNat - 152) 8 6188145).readLE k 8 = v := fun k v hk h => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h
  obtain ⟨q1, q3⟩ := rshQ (z := p) (n := xl - sh / 64) (x := x + 8 * (sh / 64)) (r := sh % 64)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k1)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k2)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k3)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152]; exact kk _ _ (by omega) k4) hq
  simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152,
    show (s.regs 4).toNat - 152 + 64 = (s.regs 4).toNat - 88 by omega,
    show (s.regs 4).toNat - 152 + 72 = (s.regs 4).toNat - 80 by omega] at q1 q3
  have hP : MemFrame M (C.mem.writeLE ((s.regs 4).toNat - 152) 8 6188145)
      [((s.regs 4).toNat - 152, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 64),
        ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)],
     fun a n v => by rw [Janus.Arm64.Memory.accessible_writeLE, hF.accessible]⟩
  obtain ⟨hF1, hLF1, hval⟩ := shift_facts (C := C.mem.writeLE ((s.regs 4).toNat - 152) 8 6188145) (w := w) h hP
    (by simp only [need]; exact q1) (by simp only [need]; exact q3)
  have rw' : ∀ a, ((s.regs 4).toNat - 80 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) →
      w.readLE a 8 = C.mem.readLE a 8 := fun a ha => by
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact kk _ _ (by omega) rfl
  have w5 := (rw' _ (by omega)).trans k5
  have w6 := (rw' _ (by omega)).trans k6
  have w7 := (rw' _ (by omega)).trans k7
  have wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    have := h.tls; have := h.trt
    rw [q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hP.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h.tls
  have wtacc : w.accessible (s.fsBase.toNat - 8) 8 false = true := by
    rw [q3.accessible, hP.accessible]; exact h.tacc
  have hsacc' : w.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true := by
    rw [q3.accessible, hP.accessible]; exact h.sacc
  refine shiftT impl b R L zp zc x xl sh s p c L' b' M h w hF1 hLF1 hinvw hval w5 w6 (by simp only [need]; exact w7)
    wtl wtacc hsacc' _ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf

end FvModexp.Amd64.Rsh
