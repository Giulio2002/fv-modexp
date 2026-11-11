import FvModexp.Proofs.Arm64.Nat.LshFin
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.lsh` (arm64): the `s % 64 = 0` path from the join of `z.make(n + 1)` (`+0x16c`) to the clear point

Spills `SP - 24 = p`, `SP - 80 = c`, `SP - 32 = s/64`; `AND $63, R6; CBNZ` (not taken); `copy(z[n-m:n], x)` =
`memmove(p + 8 (s/64), x, 8 m)` (skipped when the pointers agree — impossible here: `0 < s/64` and `z` apart from `x`
or `z = x`); reloads; `z[n] = 0`; `JMP` to `hClr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh

abbrev hJoin : Nat := segAddr Extracted.program fn + 0x16c

set_option maxRecDepth 20000 in
/-- memory facts after `memmove` and `z[n] = 0` (pure) -/
theorem copy_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M m : Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0)
    (hF : MemFrame (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8
      (sh / 64)) m (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)] ++ [(p + 8 * (sh / 64), p + 8 * (sh / 64) + 8 * xl)]))
    (hLF : LiveFrame (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8
      (sh / 64)) m L' [(p + 8 * (sh / 64), p + 8 * (sh / 64) + 8 * xl)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' m))
    (hcp : Mem.Copied (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8
      (sh / 64)) m (p + 8 * (sh / 64)) x (8 * xl)) :
    MemFrame M (m.writeLE (p + 8 * (xl + sh / 64)) 8 0) (R.rt ++ ws s p c) ∧
    LiveFrame M (m.writeLE (p + 8 * (xl + sh / 64)) 8 0) L' [(p, p + 8 * c)] ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' (m.writeLE (p + 8 * (xl + sh / 64)) 8 0)) ∧
    natVal (m.writeLE (p + 8 * (xl + sh / 64)) 8 0) (p + 8 * (sh / 64)) (xl + 1) =
      natVal s.mem x xl * 2 ^ (sh % 64) := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt
  simp only [need] at hcap
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hW : MemFrame M (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE
      (s.sp.toNat - 32) 8 (sh / 64)) [(s.sp.toNat - 80, s.sp.toNat - 72), (s.sp.toNat - 32, s.sp.toNat - 16)] := by
    janus_frame
  have hS : MemFrame m (m.writeLE (p + 8 * (xl + sh / 64)) 8 0) [(p + 8 * (xl + sh / 64), p + 8 * (xl + sh / 64) + 8)] := by
    janus_frame
  have hA : MemFrame M m (R.rt ++ ws s p c) := hW.trans hF fun a k ho => by
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2', h3'⟩ := ho
    exact ⟨⟨by omega, by omega⟩, ⟨hr, by omega, by omega⟩, by omega⟩
  refine ⟨hA.trans hS fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hS.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · exact inv_store_held hinv (h.pheld.sub (by omega) (by omega))
  · have hcp' := Asm.readLE_of_copied hcp
    rw [show p + 8 * (xl + sh / 64) = p + 8 * (sh / 64) + 8 * xl by omega, natVal_store_top _ _ _ _ (by decide)]
    simp only [natVal] at hcp' ⊢
    rw [hcp', hW.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      h.xr _ _ (Nat.le_refl _) (Nat.le_refl _), hr0]
    simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `memmove`: reloads, `z[n] = 0`, `JMP hClr`, then `fromClr` -/
theorem copyT (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0) (m : Memory)
    (hF : MemFrame (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8
      (sh / 64)) m (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)] ++ [(p + 8 * (sh / 64), p + 8 * (sh / 64) + 8 * xl)]))
    (hLF : LiveFrame (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8
      (sh / 64)) m L' [(p + 8 * (sh / 64), p + 8 * (sh / 64) + 8 * xl)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' m))
    (hcp : Mem.Copied (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8
      (sh / 64)) m (p + 8 * (sh / 64)) x (8 * xl))
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x1b4))
    (hsp : T.sp = s.sp - 160#64) (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 168#64)
    (h18 : T.regs 18 = s.regs 18) (hm : T.mem = m) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) T fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  obtain ⟨hF1, hLF1, hinv2, hval⟩ := copy_facts h hr0 hF hLF hinv hcp
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hc40 := h.c40
  have hn16 := h.n16
  have hwrt := h.wrt
  simp only [need] at hcap hn16
  unfold Apart at hpw
  have hrd : ∀ a, (s.sp.toNat - 128 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → m.readLE a 8 =
      (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8 (sh / 64)).readLE a 8 :=
    fun a ha => hF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have r24 : m.readLE (s.sp.toNat - 24) 8 = p := by
    rw [hrd _ (by omega)]; janus_simp
  have r80 : m.readLE (s.sp.toNat - 80) 8 = c := by
    rw [hrd _ (by omega)]; janus_simp
  have r32 : m.readLE (s.sp.toNat - 32) 8 = sh / 64 := by
    rw [hrd _ (by omega)]; janus_simp
  have r48 : m.readLE (s.sp.toNat - 48) 8 = xl + sh / 64 + 1 := by
    rw [hrd _ (by omega)]; janus_simp; have := h.sn1; simp only [need] at this; exact this
  have r40 : m.readLE (s.sp.toNat - 40) 8 = xl + sh / 64 := by
    rw [hrd _ (by omega)]; janus_simp; exact h.sn
  have r56 : m.readLE (s.sp.toNat + 56) 8 = sh := by
    rw [hrd _ (by omega)]; janus_simp; exact h.ssh
  have hacc : m.accessible (p + 8 * (xl + sh / 64)) 8 true = true := by
    rw [hF.accessible]; janus_simp
    exact Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hal := h.al; have hsp1 := h.sp1
  have hsacc : m.accessible (s.sp.toNat - 4256) (4256 + 64) true = true := by
    rw [hF.accessible]; janus_simp; exact h.sacc
  janus_run [hm, r24, r80, r32, r48, r40, r56] until [hClr]
  refine fromClr impl R hmc b L zp zc x xl sh s p c L' b' M h _ hF1 hLF1 hinv2 hval ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · exact (Memory.readLE_writeLE_of_disjoint (m := m) 0 (by omega)).trans r24
  · exact (Memory.readLE_writeLE_of_disjoint (m := m) 0 (by omega)).trans r48
  · exact (Memory.readLE_writeLE_of_disjoint (m := m) 0 (by omega)).trans r80
  all_goals try janus_simp
  all_goals (congr 1; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyM (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibLsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh) (h7 : S.regs 7 = BitVec.ofNat 64 (xl + sh / 64))
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hx48 := h.x48; have hxl0 := h.xl0; have hsh0 := h.sh0
  have r1 := h.lr; have r2 := h.fp; have rsh := h.ssh; have rn := h.sn; have rn1 := h.sn1
  have hsacc := h.sacc; have hal := h.al
  simp only [need] at hcap hn16 rn1 h1
  have hq0 : 0 < sh / 64 := by omega
  have hsh : sh < 2 ^ 64 := by omega
  have hq := lsr6 sh hsh
  have hq' := shr6 sh hsh
  have hpacc : M.accessible (p + 8 * (sh / 64)) (8 * xl) true = true :=
    Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : M.accessible x (8 * xl) false = true := h.xacc
  have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw
  have hph : Held R L' (p + 8 * (sh / 64)) (8 * xl) := h.pheld.sub (by omega) (by omega)
  have hph' : InRanges (p + 8 * (sh / 64)) (8 * xl) L' ∨ Outside (p + 8 * (sh / 64)) (8 * xl) R.rt := hph
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * xl] := fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc
  have hgok : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 160 := by rw [h.grd]; have := h.gok; omega
  have hxl8 : 8 * (BitVec.ofNat 64 xl).toNat % 18446744073709551616 = 8 * xl := by
    simp only [BitVec.toNat_ofNat]; omega
  have hpx : p + 8 * (sh / 64) ≠ x := by
    rcases h.px with e | e
    · omega
    · unfold Apart at e; omega
  have hinvW : R.inv b' L' (s.regs 28).toNat (view R.rt L' (((M.writeLE (s.sp.toNat - 24) 8 p).writeLE
      (s.sp.toNat - 80) 8 c).writeLE (s.sp.toNat - 32) 8 (sh / 64))) :=
    inv_store_out (inv_store_out (inv_store_out h.inv (hwrt.of_sub (by omega) (by omega)))
      (hwrt.of_sub (by omega) (by omega))) (hwrt.of_sub (by omega) (by omega))
  have hLs2 : ∀ r ∈ L', (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 160 - 4096 ∨ s.sp.toNat - 160 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 160 + 8 ∨ s.sp.toNat - 160 + 8 + 24 ≤ r.1) := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  have hxpre : M.readLE x (8 * xl) = natVal s.mem x xl := h.xr _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hr0' : (BitVec.ofNat 64 sh &&& 63#64) = 0#64 := by
    have e : sh &&& 63 = sh % 64 := Nat.and_two_pow_sub_one_eq_mod sh 6
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, e, hr0]
  have hmk := slice_mask (sh / 64) c (by omega) hc40
  have hpq : (p + 8 * (sh / 64)) % 18446744073709551616 = p + 8 * (sh / 64) := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, r1, r2, rsh, rn, rn1, hq, hq', hr0', hxl8, hmk, hpq] until [segAddr Extracted.program fn + 0x1b4, segAddr Extracted.program fn + 0x1cc] calls [hmv]
  rename_i _ _ _ m _ _ hF2 hLF2 hinv2 hcp
  refine copyT impl R hmc b L zp zc x xl sh s p c L' b' M h hr0 m hF2 hLF2 hinv2 hcp _ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals janus_simp

end FvModexp.Arm64.Lsh
