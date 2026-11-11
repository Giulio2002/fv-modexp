import FvModexp.Proofs.Amd64.Nat.RshFin
import FvModexp.Proofs.Common.AsmVW
import FvModexp.Proofs.Common.BitArith

/-!
# `nat.rsh` (amd64): the `s % 64 = 0` path from the join of `z.make(n)` (`+0x1fe`) to the norm head

Spills `e - 72 = c`, `e - 80 = n`, `e - 24 = p`; `ANDL $0x3f, DX; TESTQ; JNE` (not taken); `x[m-n:]` (`q = m - n`,
mask, `x + 8q`); `copy(z, x[m-n:])` = `memmove(p, x + 8q, 8n)` (`+0x253`; skipped when the pointers agree —
impossible: `z` apart from `x`); reloads `AX, CX, DI`; to `hNorm`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

/-- the memory after the spills and the `CALL`'s return-address push -/
@[reducible] def mW (s : State) (M : Janus.Arm64.Memory) (c n p ra : Nat) : Janus.Arm64.Memory :=
  (((M.writeLE ((s.regs 4).toNat - 72) 8 c).writeLE ((s.regs 4).toNat - 80) 8 n).writeLE ((s.regs 4).toNat - 24) 8 p
    ).writeLE ((s.regs 4).toNat - 152) 8 ra

set_option maxRecDepth 20000 in
/-- memory facts after `memmove` (pure) -/
theorem copy_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M m : Janus.Arm64.Memory} {ra : Nat}
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0)
    (hF : MemFrame (mW s M c (need xl sh) p ra) m (R.rt ++ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)] ++ [(p, p + need xl sh * 8)]))
    (hLF : LiveFrame (mW s M c (need xl sh) p ra) m L' [(p, p + need xl sh * 8)])
    (hcp : Mem.Copied (mW s M c (need xl sh) p ra) m p (x + 8 * (sh / 64)) (need xl sh * 8)) :
    MemFrame M m (R.rt ++ ws s p c) ∧ LiveFrame M m L' [(p, p + 8 * c)] ∧
    natVal m p (need xl sh) = natVal s.mem x xl / 2 ^ sh := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hpx := h.px; have hn0 := h.n0; have hx48 := h.x48
  simp only [need] at hcap hn0
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hpx
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hW : MemFrame M (mW s M c (need xl sh) p ra) [((s.regs 4).toNat - 152, (s.regs 4).toNat - 144),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 64), ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] := by
    simp only [mW]; janus_frame
  refine ⟨hW.trans hF fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_⟩
  · simp only [ws, need, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega⟩, ⟨hr, by omega, by omega⟩, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [need, outside_cons, outside_nil, and_true] at this ho
    rw [hLF.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [need, outside_cons, outside_nil, and_true]; omega),
      hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · have hcp' := Asm.readLE_of_copied hcp
    have hsh : sh = 64 * (sh / 64) := by omega
    simp only [natVal] at hcp' ⊢
    rw [show 8 * need xl sh = need xl sh * 8 by omega, hcp',
      hW.readLE _ _ (by simp only [need, outside_cons, outside_nil, and_true]; omega),
      show need xl sh * 8 = 8 * need xl sh by omega]
    have := val_hi M x (sh / 64) (need xl sh)
    simp only [natVal] at this
    rw [this, show sh / 64 + need xl sh = xl by simp only [need]; omega,
      h.xr _ _ (Nat.le_refl _) (Nat.le_refl _), ← hsh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `memmove`: reloads, to `hNorm`, then `fromNorm` -/
theorem copyT (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0) (m : Janus.Arm64.Memory) (ra : Nat)
    (hF : MemFrame (mW s M c (need xl sh) p ra) m (R.rt ++ [((s.regs 4).toNat - 152 - 4096, (s.regs 4).toNat - 152),
        ((s.regs 4).toNat - 152 + 8, (s.regs 4).toNat - 152 + 8 + 24)] ++ [(p, p + need xl sh * 8)]))
    (hLF : LiveFrame (mW s M c (need xl sh) p ra) m L' [(p, p + need xl sh * 8)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' m))
    (hcp : Mem.Copied (mW s M c (need xl sh) p ra) m p (x + 8 * (sh / 64)) (need xl sh * 8))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x258))
    (hsp : T.regs 4 = s.regs 4 - 144#64) (h14 : T.regs 14 = s.regs 14) (h5 : T.regs 5 = s.regs 4 - 8#64)
    (hx15 : T.xmm 15 = s.xmm 15) (hfs : T.fsBase = s.fsBase) (hdf : T.df = false) (hm : T.mem = m) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) T fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  obtain ⟨hF1, hLF1, hval⟩ := copy_facts h hr0 hF hLF hcp
  have hsp0 := h.sp0; have hwrt := h.wrt; have hp48 := h.p48; have hc40 := h.c40; have hcap := h.cap
  have hx16 := h.xl16
  simp only [need] at hcap
  have hrd : ∀ a, ((s.regs 4).toNat - 120 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → m.readLE a 8 =
      (mW s M c (need xl sh) p ra).readLE a 8 :=
    fun a ha => hF.readLE _ _ (by
      have := h.pw; unfold Apart at this
      simp only [need, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have r24 : m.readLE ((s.regs 4).toNat - 24) 8 = p := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r72 : m.readLE ((s.regs 4).toNat - 72) 8 = c := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r80 : m.readLE ((s.regs 4).toNat - 80) 8 = need xl sh := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp; simp only [need]; omega
  have hal := h.al; have hsp1 := h.sp1
  have hsacc : m.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true := by
    rw [hF.accessible]; simp only [mW]; janus_simp; exact h.sacc
  janus64_run [hm, r24, r72, r80, BitVec.msb_eq_decide] until [hNorm]
  refine fromNorm impl b R L zp zc x xl sh s p c L' b' M h _ hF1 hLF1 hinv hval _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyM (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl xc sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 = 0) (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h3 : S.regs 3 = BitVec.ofNat 64 (need xl sh))
    (h2 : S.regs 2 = BitVec.ofNat 64 sh) (h6 : S.regs 6 = BitVec.ofNat 64 xl)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 (need xl sh))
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48; have hn0 := h.n0
  have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  simp only [need] at hcap hn0 h3 h9
  have hsh : sh < 2 ^ 64 := by omega
  have hq8 : 8 * (sh / 64) < 2 ^ 64 := by omega
  have hs3 := shl3 (sh / 64) hq8
  have hxq : BitVec.ofNat 64 xl - BitVec.ofNat 64 (xl - sh / 64) = BitVec.ofNat 64 (sh / 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hxn : BitVec.ofNat 64 xl - BitVec.ofNat 64 (sh / 64) = BitVec.ofNat 64 (xl - sh / 64) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hmask : ((BitVec.ofNat 64 (sh / 64) - BitVec.ofNat 64 xc).sshiftRight 63 &&& BitVec.ofNat 64 (8 * (sh / 64))) =
      BitVec.ofNat 64 (8 * (sh / 64)) :=
    sub_sshr63_and _ _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hxq1 : BitVec.ofNat 64 (8 * (sh / 64)) + BitVec.ofNat 64 x = BitVec.ofNat 64 (x + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hxq2 : BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * (sh / 64)) = BitVec.ofNat 64 (x + 8 * (sh / 64)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hpx := h.px
  unfold Apart at hpx
  have hne : ((18446744073709551616 - (x + 8 * (sh / 64)) + p) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; omega
  have hr0' : BitVec.ofNat 64 sh &&& 63#64 = 0#64 := by
    have e : sh &&& 63 = sh % 64 := Nat.and_two_pow_sub_one_eq_mod sh 6
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, e, hr0]
  have hx15' := h.x15; have hra := h.ra47; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpf := h.pf; have htw := h.tw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw hpg hpf htw
  have hpacc' : M.accessible p ((xl - sh / 64) * 8) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : M.accessible (x + 8 * (sh / 64)) ((xl - sh / 64) * 8) false = true :=
    Janus.Arm64.Memory.accessible_mono _ h.xacc (by omega) (by omega)
  have hph : InRanges p ((xl - sh / 64) * 8) L' ∨ Outside p ((xl - sh / 64) * 8) R.rt :=
    h.pheld.sub (by omega) (by omega)
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, (xl - sh / 64) * 8] :=
    fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc; have htacc := h.tacc; have htls := h.tls; have htb := h.tlsg.base; have htrt := h.trt
  have hgok : M.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 152 := by
    rw [h.grd]; have := h.gok; omega
  have hinv := h.inv
  janus64_run [hm, hfs, hs3, hxq, hxn, hmask, hxq1, hxq2, hne, hr0', BitVec.msb_eq_decide]
    until [segAddr Extracted.program fn + 0x258] calls [hmv]
  rename_i _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp
  refine copyT impl R b L zp zc x xl sh s p c L' b' M h hr0 m _ hF2 hLF2 hinv2 hcp _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf

end FvModexp.Amd64.Rsh
