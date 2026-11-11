import FvModexp.Proofs.Amd64.Nat.LshFin
import FvModexp.Proofs.Common.AsmVW
import FvModexp.Proofs.Common.BitArith
import FvModexp.Proofs.Common.SetBytesMath

/-!
# `nat.lsh` (amd64): the `s % 64 = 0` path from the join of `z.make(n + 1)` (`+0x1d1`) to the clear point

Spills `e - 24 = p`, `e - 80 = c`; `ANDL $0x3f, R9; TESTQ; JNE` (not taken); `CMPQ CX, R10; JB panic`;
`copy(z[n-m:n], x)` = `memmove(p + 8 (s/64), x, 8 m)` (`+0x217`; skipped when the pointers agree — impossible here:
`0 < s/64` and `z` apart from `x` or `z = x`); reloads; `CMPQ DX, R10; JBE panic`; `z[n] = 0`; `JMP` to `hClr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Lsh

/-- the memory after the spills and the `CALL`'s return-address push -/
@[reducible] def mW (s : State) (M : Janus.Arm64.Memory) (p c ra : Nat) : Janus.Arm64.Memory :=
  ((M.writeLE ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 80) 8 c).writeLE ((s.regs 4).toNat - 152) 8 ra

set_option maxRecDepth 20000 in
/-- memory facts after `memmove` and `z[n] = 0` (pure) -/
theorem copy_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M m : Janus.Arm64.Memory} {ra : Nat}
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0)
    (hF : MemFrame (mW s M p c ra) m (R.rt ++ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)] ++
      [(p + 8 * (sh / 64), p + 8 * (sh / 64) + xl * 8)]))
    (hLF : LiveFrame (mW s M p c ra) m L' [(p + 8 * (sh / 64), p + 8 * (sh / 64) + xl * 8)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' m))
    (hcp : Mem.Copied (mW s M p c ra) m (p + 8 * (sh / 64)) x (xl * 8)) :
    MemFrame M (m.writeLE (p + (xl + sh / 64) * 8) 8 0) (R.rt ++ ws s p c) ∧
    LiveFrame M (m.writeLE (p + (xl + sh / 64) * 8) 8 0) L' [(p, p + 8 * c)] ∧
    R.inv b' L' (s.regs 14).toNat (view R.rt L' (m.writeLE (p + (xl + sh / 64) * 8) 8 0)) ∧
    natVal (m.writeLE (p + (xl + sh / 64) * 8) 8 0) (p + 8 * (sh / 64)) (xl + 1) =
      natVal s.mem x xl * 2 ^ (sh % 64) := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt
  simp only [need] at hcap
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hW : MemFrame M (mW s M p c ra) [((s.regs 4).toNat - 152, (s.regs 4).toNat - 144),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] := by
    simp only [mW]; janus_frame
  have hS : MemFrame m (m.writeLE (p + (xl + sh / 64) * 8) 8 0)
      [(p + (xl + sh / 64) * 8, p + (xl + sh / 64) * 8 + 8)] := by janus_frame
  have hA : MemFrame M m (R.rt ++ ws s p c) := hW.trans hF fun a k ho => by
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega⟩, ⟨hr, by omega, by omega⟩, by omega⟩
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
    rw [show p + (xl + sh / 64) * 8 = p + 8 * (sh / 64) + 8 * xl by omega, natVal_store_top _ _ _ _ (by decide)]
    simp only [natVal] at hcp' ⊢
    rw [show 8 * xl = xl * 8 by omega, hcp', hW.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      show xl * 8 = 8 * xl by omega, h.xr _ _ (Nat.le_refl _) (Nat.le_refl _), hr0]
    simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `memmove`: reloads, `z[n] = 0`, `JMP hClr`, then `fromClr` -/
theorem copyT (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0) (m : Janus.Arm64.Memory) (ra : Nat)
    (hF : MemFrame (mW s M p c ra) m (R.rt ++ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)] ++
      [(p + 8 * (sh / 64), p + 8 * (sh / 64) + xl * 8)]))
    (hLF : LiveFrame (mW s M p c ra) m L' [(p + 8 * (sh / 64), p + 8 * (sh / 64) + xl * 8)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' m))
    (hcp : Mem.Copied (mW s M p c ra) m (p + 8 * (sh / 64)) x (xl * 8))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x21c))
    (hsp : T.regs 4 = s.regs 4 - 144#64) (h14 : T.regs 14 = s.regs 14) (h5 : T.regs 5 = s.regs 4 - 8#64)
    (hx15 : T.xmm 15 = s.xmm 15) (hfs : T.fsBase = s.fsBase) (hdf : T.df = false) (hm : T.mem = m) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) T fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hF1, hLF1, hinv2, hval⟩ := copy_facts h hr0 hF hLF hinv hcp
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hc40 := h.c40
  have hn16 := h.n16
  have hwrt := h.wrt
  simp only [need] at hcap hn16
  unfold Apart at hpw
  have hrd : ∀ a, ((s.regs 4).toNat - 120 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → m.readLE a 8 =
      (mW s M p c ra).readLE a 8 :=
    fun a ha => hF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have r24 : m.readLE ((s.regs 4).toNat - 24) 8 = p := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r80 : m.readLE ((s.regs 4).toNat - 80) 8 = c := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r56 : m.readLE ((s.regs 4).toNat - 56) 8 = xl + sh / 64 + 1 := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp; have := h.sn1; simp only [need] at this; exact this
  have r48 : m.readLE ((s.regs 4).toNat - 48) 8 = xl + sh / 64 := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp; exact h.sn
  have r40 : m.readLE ((s.regs 4).toNat - 40) 8 = sh / 64 := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp; exact h.sq
  have hacc : m.accessible (p + (xl + sh / 64) * 8) 8 true = true := by
    rw [hF.accessible]; simp only [mW]; janus_simp
    exact Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hal := h.al; have hsp1 := h.sp1
  have hsacc : m.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true := by
    rw [hF.accessible]; simp only [mW]; janus_simp; exact h.sacc
  janus64_run [hm, r24, r80, r56, r48, r40, BitVec.msb_eq_decide] until [hClr]
  refine fromClr impl R hmc b L zp zc x xl sh s p c L' b' M h _ hF1 hLF1 hinv2 hval ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) 0 (by omega)).trans r24
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) 0 (by omega)).trans r56
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) 0 (by omega)).trans r80
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyM (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibLsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h2 : S.regs 2 = BitVec.ofNat 64 (need xl sh))
    (h3 : S.regs 3 = BitVec.ofNat 64 (sh / 64)) (h6 : S.regs 6 = BitVec.ofNat 64 xl)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h8 : S.regs 8 = BitVec.ofNat 64 xc) (h9 : S.regs 9 = BitVec.ofNat 64 sh)
    (h10 : S.regs 10 = BitVec.ofNat 64 (xl + sh / 64))
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hx48 := h.x48; have hxl0 := h.xl0; have hsh0 := h.sh0
  have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  simp only [need] at hcap hn16 h2
  have hq0 : 0 < sh / 64 := by omega
  have hsh : sh < 2 ^ 64 := by omega
  have hq8 : 8 * (sh / 64) < 2 ^ 64 := by omega
  have hmask : ((BitVec.ofNat 64 (sh / 64) - BitVec.ofNat 64 c).sshiftRight 63 &&& BitVec.ofNat 64 (8 * (sh / 64))) =
      BitVec.ofNat 64 (8 * (sh / 64)) :=
    sub_sshr63_and _ _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hpx : p + 8 * (sh / 64) ≠ x := by
    rcases h.px with e | e
    · omega
    · unfold Apart at e; omega
  have hpx' : (BitVec.ofNat 64 x = BitVec.ofNat 64 (p + 8 * (sh / 64))) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hne : ((18446744073709551616 - (p + 8 * (sh / 64)) + x) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; apply hpx; omega
  have hs3 := shl3 (sh / 64) hq8
  have hpq1 : BitVec.ofNat 64 (8 * (sh / 64)) + BitVec.ofNat 64 p = BitVec.ofNat 64 (p + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hpq2 : BitVec.ofNat 64 p + BitVec.ofNat 64 (8 * (sh / 64)) = BitVec.ofNat 64 (p + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hr0' : BitVec.ofNat 64 sh &&& 63#64 = 0#64 := by
    have e : sh &&& 63 = sh % 64 := Nat.and_two_pow_sub_one_eq_mod sh 6
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, e, hr0]
  have hx15' := h.x15; have hra := h.ra47; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpf := h.pf; have htw := h.tw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw hpg hpf htw
  have hpacc' : M.accessible (p + 8 * (sh / 64)) (xl * 8) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : M.accessible x (xl * 8) false = true := by rw [show xl * 8 = 8 * xl by omega]; exact h.xacc
  have hph : InRanges (p + 8 * (sh / 64)) (xl * 8) L' ∨ Outside (p + 8 * (sh / 64)) (xl * 8) R.rt :=
    h.pheld.sub (by omega) (by omega)
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, xl * 8] := fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc; have htacc := h.tacc; have htls := h.tls; have htb := h.tlsg.base; have htrt := h.trt
  have hgok : M.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 152 := by
    rw [h.grd]; have := h.gok; omega
  have hinv := h.inv
  janus64_run [hm, hfs, hmask, hs3, hpq1, hpq2, hpx', hne, hr0', BitVec.msb_eq_decide]
    until [segAddr Extracted.program fn + 0x21c] calls [hmv]
  rename_i _ _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp
  refine copyT impl R hmc b L zp zc x xl sh s p c L' b' M h hr0 m _ hF2 hLF2 hinv2 hcp _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf
end FvModexp.Amd64.Lsh
