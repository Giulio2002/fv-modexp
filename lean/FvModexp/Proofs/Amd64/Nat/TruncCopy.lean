import FvModexp.Proofs.Amd64.Nat.TruncNorm
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.trunc` (amd64): main path from the join of `z.make(w)` (`+0xbb`) to `TESTQ` (`+0x100`), then `fromTst`

`CMPQ SI, BX; MOVQ BX, DX; CMOVL SI, BX` (`min(len x, w) = w`); `CMPQ DI, AX; JE` (Go's `copy` skips `memmove` when
the pointers agree); spills `e - 24 = p`, `e - 40 = w`, `e - 64 = c`; `memmove(p, x, 8 w)` (`+0xe3`, returns to
`+0xe8`); reloads `AX, CX, DX, R9`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

/-- the memory after the spills and the `CALL`'s return-address push -/
@[reducible] def mW (s : State) (M : Janus.Arm64.Memory) (p w c ra : Nat) : Janus.Arm64.Memory :=
  (((M.writeLE ((s.regs 4).toNat - 24) 8 p).writeLE ((s.regs 4).toNat - 40) 8 w).writeLE
    ((s.regs 4).toNat - 64) 8 c).writeLE ((s.regs 4).toNat - 96) 8 ra

theorem x_low {M : Janus.Arm64.Memory} {m0 : Janus.Arm64.Memory} {x xl w : Nat} (hw : w ≤ xl)
    (hxr : ∀ a k, x ≤ a → a + k ≤ x + 8 * xl → M.readLE a k = m0.readLE a k) :
    M.readLE x (8 * w) = natVal m0 x xl % 2 ^ (64 * w) := by
  rw [← Janus.Arm64.Memory.readLE_mod M x (8 * xl) (8 * w) (by omega), hxr _ _ (Nat.le_refl _) (Nat.le_refl _),
    show (256 : Nat) ^ (8 * w) = 2 ^ (64 * w) by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega]

set_option maxRecDepth 20000 in
/-- memory facts after `memmove` (pure) -/
theorem copy_facts {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl n : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M m : Janus.Arm64.Memory} {ra : Nat}
    (h : Mid R b L zp zc x xl n s (wOf n) p c L' b' M)
    (hF : MemFrame (mW s M p (wOf n) c ra) m (R.rt ++ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96),
        ((s.regs 4).toNat - 96 + 8, (s.regs 4).toNat - 96 + 8 + 24)] ++ [(p, p + 8 * wOf n)]))
    (hLF : LiveFrame (mW s M p (wOf n) c ra) m L' [(p, p + 8 * wOf n)])
    (hcp : Mem.Copied (mW s M p (wOf n) c ra) m p x (8 * wOf n)) :
    MemFrame M m (R.rt ++ ws s p c) ∧ LiveFrame M m L' [(p, p + 8 * c)] ∧
    natVal m p (wOf n) = natVal s.mem x xl % 2 ^ (64 * wOf n) := by
  have hsp0 := h.sp0; have hcap := h.cap; have hp48 := h.p48; have hpw := h.pw; have hxw := h.xw
  have hwrt := h.wrt; have hkx := h.kx
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hW : MemFrame M (mW s M p (wOf n) c ra) [((s.regs 4).toNat - 96, (s.regs 4).toNat - 88),
      ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32),
      ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)] := by
    simp only [mW]; janus_frame
  refine ⟨hW.trans hF fun a k ho => ?_, ⟨fun a k hin ho => ?_⟩, ?_⟩
  · simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2'⟩ := ho
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, ⟨hr, by omega, by omega⟩, by omega⟩
  · obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hLF.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  · have hcp' := Asm.readLE_of_copied hcp
    simp only [natVal]
    rw [hcp', hW.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact x_low hkx h.xr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `memmove`: reloads, then `fromTst` -/
theorem copyT (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl n s (wOf n) p c L' b' M) (hk : wOf n = EvenHyp.truncNeed xl n) (hn : n ≤ 2 ^ 20)
    (m : Janus.Arm64.Memory) (ra : Nat)
    (hF : MemFrame (mW s M p (wOf n) c ra) m (R.rt ++ [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96),
        ((s.regs 4).toNat - 96 + 8, (s.regs 4).toNat - 96 + 8 + 24)] ++ [(p, p + 8 * wOf n)]))
    (hLF : LiveFrame (mW s M p (wOf n) c ra) m L' [(p, p + 8 * wOf n)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' m))
    (hcp : Mem.Copied (mW s M p (wOf n) c ra) m p x (8 * wOf n))
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0xe8))
    (hsp : T.regs 4 = s.regs 4 - 88#64) (h14 : T.regs 14 = s.regs 14) (h5 : T.regs 5 = s.regs 4 - 8#64)
    (hx15 : T.xmm 15 = s.xmm 15) (hfs : T.fsBase = s.fsBase) (hdf : T.df = false) (hm : T.mem = m) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) T fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  obtain ⟨hF1, hLF1, hval⟩ := copy_facts h hF hLF hcp
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hwrt := h.wrt; have hcap := h.cap; have hp48 := h.p48
  have hc40 := h.c40
  have hrd : ∀ a, ((s.regs 4).toNat - 64 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 64) → m.readLE a 8 =
      (mW s M p (wOf n) c ra).readLE a 8 :=
    fun a ha => hF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by
        have := h.pw; unfold Apart at this; omega⟩)
  have r24 : m.readLE ((s.regs 4).toNat - 24) 8 = p := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r40 : m.readLE ((s.regs 4).toNat - 40) 8 = wOf n := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r64 : m.readLE ((s.regs 4).toNat - 64) 8 = c := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp
  have r38 : m.readLE ((s.regs 4).toNat + 0x38) 8 = n := by
    rw [hrd _ (by omega)]; simp only [mW]; janus_simp; exact h.sn rfl
  have hal := h.al
  have hsacc : m.accessible ((s.regs 4).toNat - 4192) (4192 + 64) true = true := by
    rw [hF.accessible]; simp only [mW]; janus_simp; exact h.sacc
  janus64_run [hm, r24, r40, r64, r38] until [hTst]
  refine fromTst impl R b L zp zc x xl n s p c L' b' M h hk hn m hF1 hLF1 hinv hval _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ rfl
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyM (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl n s (wOf n) p c L' b' M) (hk : wOf n = EvenHyp.truncNeed xl n) (hn : n ≤ 2 ^ 20)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hJoin) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h3 : S.regs 3 = BitVec.ofNat 64 (wOf n)) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 n)
    (hsp : S.regs 4 = s.regs 4 - 88#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48; have hkx := h.kx
  have hmin : (if (xl : Int) < (wOf n : Int) then BitVec.ofNat 64 xl else BitVec.ofNat 64 (wOf n)) =
      BitVec.ofNat 64 (wOf n) := by rw [if_neg (by omega)]
  by_cases hpx : p = x
  · subst hpx
    have hval : natVal M p (wOf n) = natVal s.mem p xl % 2 ^ (64 * wOf n) := x_low hkx h.xr
    have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
    janus64_run [hm, hmin, hwm, BitVec.msb_eq_decide] until [hTst]
    refine fromTst impl R b L zp zc p xl n s p c L' b' M h hk hn M (MemFrame.refl _ _) (LiveFrame.refl _ _ _) h.inv
      hval _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hfs | exact hdf | skip
  · have hsacc := h.sacc; have hal := h.al
    have hpacc : M.accessible p (8 * wOf n) true = true :=
      Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
    have hxacc : M.accessible x (8 * wOf n) false = true :=
      Janus.Arm64.Memory.accessible_mono _ h.xacc (Nat.le_refl _) (by omega)
    have hx15' := h.x15; have hra := h.ra47; have hwrt := h.wrt
    have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpf := h.pf; have htw := h.tw
    have hxw := h.xw
    simp only [win, outside_cons, outside_nil, and_true] at hxw
    unfold Apart at hpw hgw hpg hpf htw
    have hph : InRanges p (8 * wOf n) L' ∨ Outside p (8 * wOf n) R.rt := h.pheld.sub (Nat.le_refl _) (by omega)
    have hLs := h.lsep
    simp only [LiveSep, win] at hLs
    have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * wOf n] := fun d src => h.sv.2.1 d src _ (by omega)
    have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
    have hgacc := h.gacc; have htacc := h.tacc; have htls := h.tls; have htb := h.tlsg.base; have htrt := h.trt
    have hgok : M.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 96 := by
      rw [h.grd]; have := h.gok; omega
    have hinv := h.inv
    have hs3 : BitVec.ofNat 64 (wOf n) <<< 3 = BitVec.ofNat 64 (8 * wOf n) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; unfold wOf; omega
    have hpx' : (BitVec.ofNat 64 x = BitVec.ofNat 64 p) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have hne : ((18446744073709551616 - p + x) % 18446744073709551616 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply hpx; omega
    have h8w : 8 * wOf n % 18446744073709551616 = 8 * wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
    janus64_run [hm, hfs, hmin, hs3, hpx', hne, h8w, BitVec.msb_eq_decide]
      until [segAddr Extracted.program fn + 0xe8] calls [hmv]
    rename_i m _ _ hF2 hLF2 hinv2 hcp
    refine copyT impl R b L zp zc x xl n s p c L' b' M h hk hn m _ hF2 hLF2 hinv2 hcp _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hfs | exact hdf | skip

end FvModexp.Amd64.Trunc
