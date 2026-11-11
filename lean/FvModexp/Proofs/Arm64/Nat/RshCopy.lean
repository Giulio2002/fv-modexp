import FvModexp.Proofs.Arm64.Nat.RshFin
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.rsh` (arm64): the `s % 64 = 0` path from the join of `z.make(n)` (`+0x1ac`) to the norm head

Spills `SP - 64 = c`, `SP - 72 = n`, `SP - 24 = p`; `AND $63, R6; CBNZ` (not taken); `x[m-n:]` (masked pointer
`x + 8 (s/64)`), `CSEL` (`min(n, n) = n`), `CMP R3, R0; BEQ` (pointers differ: `z` apart from `x`);
`memmove(p, x + 8 (s/64), 8 n)` (`+0x1f4`); reloads; to `hNorm`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Rsh

set_option maxRecDepth 20000 in
/-- memory facts after `memmove` (pure) -/
theorem copy_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M m : Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame (((M.writeLE (s.sp.toNat - 64) 8 c).writeLE (s.sp.toNat - 72) 8 (xl - sh / 64)).writeLE
      (s.sp.toNat - 24) 8 p) m (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
        (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 24)] ++ [(p, p + 8 * (xl - sh / 64))]))
    (hLF : LiveFrame (((M.writeLE (s.sp.toNat - 64) 8 c).writeLE (s.sp.toNat - 72) 8 (xl - sh / 64)).writeLE
      (s.sp.toNat - 24) 8 p) m L' [(p, p + 8 * (xl - sh / 64))])
    (hcp : Mem.Copied (((M.writeLE (s.sp.toNat - 64) 8 c).writeLE (s.sp.toNat - 72) 8 (xl - sh / 64)).writeLE
      (s.sp.toNat - 24) 8 p) m p (x + 8 * (sh / 64)) (8 * (xl - sh / 64))) :
    MemFrame M m (R.rt ++ ws s p c) ∧ LiveFrame M m L' [(p, p + 8 * c)] ∧
    natVal m p (need xl sh) = natVal s.mem x xl / 2 ^ (64 * (sh / 64)) := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt; have hn0 := h.xl0
  simp only [need] at hcap hn0
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hW : MemFrame M (((M.writeLE (s.sp.toNat - 64) 8 c).writeLE (s.sp.toNat - 72) 8 (xl - sh / 64)).writeLE
      (s.sp.toNat - 24) 8 p) [(s.sp.toNat - 72, s.sp.toNat - 56), (s.sp.toNat - 24, s.sp.toNat - 16)] := by
    janus_frame
  refine ⟨hW.trans hF fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2', h3'⟩ := ho
    exact ⟨⟨by omega, by omega⟩, ⟨hr, by omega, by omega⟩, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hLF.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · have hcp' := Asm.readLE_of_copied hcp
    simp only [need, natVal] at hcp' ⊢
    rw [hcp', hW.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      h.xr _ _ (by omega) (by omega)]
    have := val_hi s.mem x (sh / 64) (xl - sh / 64)
    simp only [natVal] at this
    rw [this, show sh / 64 + (xl - sh / 64) = xl by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyM (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh) (h7 : S.regs 7 = BitVec.ofNat 64 (need xl sh))
    (hsp : S.sp = s.sp - 144#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 152#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48; have hn0 := h.xl0
  have hsacc := h.sacc; have hal := h.al
  simp only [need] at hcap hn0 h1 h7
  have hsh : sh < 2 ^ 64 := by omega
  have hr0' : (BitVec.ofNat 64 sh &&& 63#64) = 0#64 := by
    have e : sh &&& 63 = sh % 64 := Nat.and_two_pow_sub_one_eq_mod sh 6
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, e, hr0]
  have hq : sh / 64 < xl := by omega
  have hmk := xmask xl xc (sh / 64) hq hxc hxc'
  have hsa := sub_add_sub xl (xl - sh / 64) (by omega) (by omega)
  have hmod : (18446744073709551616 - xl + (xl + (xl - sh / 64))) % 18446744073709551616 = xl - sh / 64 := by omega
  have hlt : (((xl - sh / 64 : Nat) : Int) < ((xl - sh / 64 : Nat) : Int)) = False := by simp
  have hxq : (x + 8 * (sh / 64)) % 18446744073709551616 = x + 8 * (sh / 64) := Nat.mod_eq_of_lt (by omega)
  have hxa : BitVec.ofNat 64 x + BitVec.ofNat 64 (sh / 64 * 8) = BitVec.ofNat 64 (x + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hpx : p ≠ x + 8 * (sh / 64) := by have := h.px; unfold Apart at this; omega
  have hpacc : M.accessible p (8 * (xl - sh / 64)) true = true :=
    Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : M.accessible (x + 8 * (sh / 64)) (8 * (xl - sh / 64)) false = true :=
    Memory.accessible_mono _ h.xacc (by omega) (by omega)
  have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw
  have hph : Held R L' p (8 * (xl - sh / 64)) := h.pheld.sub (by omega) (by omega)
  have hph' : InRanges p (8 * (xl - sh / 64)) L' ∨ Outside p (8 * (xl - sh / 64)) R.rt := hph
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * (xl - sh / 64)] :=
    fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc
  have hgok : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 144 := by rw [h.grd]; have := h.gok; omega
  have hn8 : 8 * (BitVec.ofNat 64 (xl - sh / 64)).toNat % 18446744073709551616 = 8 * (xl - sh / 64) := by
    simp only [BitVec.toNat_ofNat]; omega
  have hinvW : R.inv b' L' (s.regs 28).toNat (view R.rt L' (((M.writeLE (s.sp.toNat - 64) 8 c).writeLE
      (s.sp.toNat - 72) 8 (xl - sh / 64)).writeLE (s.sp.toNat - 24) 8 p)) :=
    inv_store_out (inv_store_out (inv_store_out h.inv (hwrt.of_sub (by omega) (by omega)))
      (hwrt.of_sub (by omega) (by omega))) (hwrt.of_sub (by omega) (by omega))
  have hLs2 : ∀ r ∈ L', (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 144 - 4096 ∨ s.sp.toNat - 144 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 144 + 8 ∨ s.sp.toNat - 144 + 8 + 24 ≤ r.1) := by
    intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
  have hxw' : x + 8 * (sh / 64) + 8 * (xl - sh / 64) ≤ s.sp.toNat - 4240 ∨ s.sp.toNat + 64 ≤ x + 8 * (sh / 64) := by
    omega
  janus_run [hm, hr0', hmk, hsa, hmod, hlt, hxq, hxa, hn8] until [segAddr Extracted.program fn + 0x1f8] calls [hmv]
  rename_i _ _ _ m _ _ hF2 hLF2 hinv2 hcp
  obtain ⟨hF1, hLF1, hval⟩ := copy_facts h hF2 hLF2 hcp
  rw [show 64 * (sh / 64) = sh by omega] at hval
  have hrd : ∀ a, (s.sp.toNat - 112 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → m.readLE a 8 =
      (((M.writeLE (s.sp.toNat - 64) 8 c).writeLE (s.sp.toNat - 72) 8 (xl - sh / 64)).writeLE
        (s.sp.toNat - 24) 8 p).readLE a 8 := fun a ha => hF2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have r24 : m.readLE (s.sp.toNat - 24) 8 = p := by rw [hrd _ (by omega)]; janus_simp
  have r64 : m.readLE (s.sp.toNat - 64) 8 = c := by rw [hrd _ (by omega)]; janus_simp
  have r72 : m.readLE (s.sp.toNat - 72) 8 = xl - sh / 64 := by rw [hrd _ (by omega)]; janus_simp
  have hsacc' : m.accessible (s.sp.toNat - 4240) (4240 + 64) true = true := by
    rw [hF2.accessible]; janus_simp; exact hsacc
  janus_run [r24, r64, r72] until [hNorm]
  refine fromNorm impl b R L zp zc x xl sh s p c L' b' M h m hF1 hLF1 hinv2 hval _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals janus_simp

end FvModexp.Arm64.Rsh
