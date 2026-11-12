import FvModexp.Proofs.Amd64.Nat.TruncDefs
import FvModexp.Proofs.Common.TruncMath

/-!
# `nat.trunc` (amd64): the top-word mask (`+0x100`), the inlined `z.norm()` loop (`+0x1e7`) and the return

At `hTst`: `AX = p`, `CX = c`, `DX = w`, `R9 = n`. `TESTQ $0x3f, R9; JE` (no mask) → `MOVQ CX, BX`; else
`LEAQ -1(DX), SI; CMPQ DX, SI; JBE panic; MOVQ CX, BX; SI = 1 << (n % 64) - 1; ANDQ SI, -8(AX)(DX*8)`; `JMP norm`.
Norm loop head `+0x1e7` (`TESTQ DX, DX; JLE`; `MOVQ -8(AX)(DX*8), SI; TESTQ SI; JE +0x1e4` (`DECQ DX`));
`CMPQ DX, BX; JA panic; MOVQ BX, CX; MOVQ DX, BX; ADDQ $0x50, SP; POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (natVal_drop_zero)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Amd64.Segment) (s : State) (M : Janus.Arm64.Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c → s'.fsBase = s.fsBase → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 4192 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 64 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 4192) (4192 + 64) true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hNorm → S.regs 2 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 3 = BitVec.ofNat 64 c → S.regs 4 = s.regs 4 - 88#64 →
      S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase →
      S.df = false → S.mem = M → natVal M p i = V →
      ReachesRet (LibTrunc.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Q s' := by
  have hcm : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  intro i
  induction i with
  | zero =>
    intro S hi hpc h2 h0 h1 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hcm, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfin _ 0 rfl ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hx15 | exact hdf | omega
  | succ i ih =>
    intro S hi hpc h2 h0 h1 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hcm, key, BitVec.msb_eq_decide] until [hNorm]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by first | (janus64_simp; done) | (janus64_simp; exact hx15)) (by first | (janus64_simp; done) | (janus64_simp; exact hfs))
        (by first | exact hdf | (janus64_simp; done) | (janus64_simp; exact hdf)) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfin _ (i + 1) rfl ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hx15 | exact hdf | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `TESTQ $0x3f, R9`; the top-word mask when `n % 64 ≠ 0`; to the norm loop head -/
theorem maskT (impl : List Amd64.Segment) (s : State) (M2 : Janus.Arm64.Memory) (p c n : Nat) (Q : State → Prop)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 hNorm → S'.regs 0 = BitVec.ofNat 64 p →
      S'.regs 2 = BitVec.ofNat 64 (wOf n) → S'.regs 3 = BitVec.ofNat 64 c → S'.regs 4 = s.regs 4 - 88#64 →
      S'.regs 14 = s.regs 14 → S'.regs 5 = s.regs 4 - 8#64 → S'.xmm 15 = s.xmm 15 → S'.fsBase = s.fsBase →
      S'.df = false →
      MemFrame M2 S'.mem [(p + 8 * (wOf n - 1), p + 8 * wOf n)] →
      natVal S'.mem p (wOf n) = natVal M2 p (wOf n) % 2 ^ n →
      ReachesRet (LibTrunc.program.link impl) (retAddrOf s) S' Q)
    (hn : n ≤ 2 ^ 20) (hc : wOf n ≤ c) (hc40 : c < 2 ^ 40) (hp : p + 8 * c ≤ 2 ^ 48)
    (hacc : M2.accessible p (8 * c) true = true)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hTst) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h2 : S.regs 2 = BitVec.ofNat 64 (wOf n)) (h1 : S.regs 1 = BitVec.ofNat 64 c) (h9 : S.regs 9 = BitVec.ofNat 64 n)
    (hsp : S.regs 4 = s.regs 4 - 88#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M2) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) S Q := by
  by_cases h64 : n % 64 = 0
  · have hlt : natVal M2 p (wOf n) < 2 ^ n := by
      have := natVal_lt M2 p (wOf n); rwa [show 64 * wOf n = n by unfold wOf; omega] at this
    have hr0' : BitVec.ofNat 64 n &&& 63#64 = 0#64 := by
      have e : n &&& 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), e, h64]
    janus64_run [hm, hr0', BitVec.msb_eq_decide] until [hNorm]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?v
    case v => exact (Nat.mod_eq_of_lt hlt).symm
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hfs | exact hdf | skip
  · have hw1 : 1 ≤ wOf n := by unfold wOf; omega
    have hpacc : M2.accessible p (8 * wOf n) true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    have hr0' : (BitVec.ofNat 64 n &&& 63#64 = 0#64) = False := by
      have e : n &&& 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
      simp only [eq_iff_iff, iff_false]; intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), e] at this
      omega
    janus64_run [hm, hr0', BitVec.msb_eq_decide] until [hNorm]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?fr ?v
    case fr => janus_frame
    case v =>
      dsimp only
      have h2r : 2 ^ (n % 64) % 18446744073709551616 = 2 ^ (n % 64) :=
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (m := n % 64) (n := 64) (by decide) (by omega))
      have e64 : 64 * (wOf n - 1) + n % 64 = n := by unfold wOf; omega
      rw [show p + wOf n * 8 - 8 = p + 8 * (wOf n - 1) by omega, h2r,
        TruncMath.mask_val _ _ _ _ hw1 (by omega) (by omega), e64]
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hfs | exact hdf | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `TESTQ` (memory `M2` after the copy) to the return, with the postcondition -/
theorem fromTst (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl n s (wOf n) p c L' b' M) (hk : wOf n = EvenHyp.truncNeed xl n) (hn : n ≤ 2 ^ 20)
    (M2 : Janus.Arm64.Memory) (hF1 : MemFrame M M2 (R.rt ++ ws s p c)) (hLF1 : LiveFrame M M2 L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' M2))
    (hval : natVal M2 p (wOf n) = natVal s.mem x xl % 2 ^ (64 * wOf n))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hTst) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h2 : S.regs 2 = BitVec.ofNat 64 (wOf n)) (h1 : S.regs 1 = BitVec.ofNat 64 c) (h9 : S.regs 9 = BitVec.ofNat 64 n)
    (hsp : S.regs 4 = s.regs 4 - 88#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M2) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  have hsp0 := h.sp0; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48; have hpw := h.pw
  unfold Apart at hpw
  have hws : ∀ a n, ((s.regs 4).toNat - 8 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 8) → Outside a n (R.rt ++ ws s p c) := by
    intro a n ha
    simp only [ws, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h.wrt.of_sub (by omega) (by omega), by omega, by omega⟩
  refine maskT impl s M2 p c n _ (fun S' hpc' h0' h2' h3' hsp' h14' h5' hx' hfs' hdf' hF3 hv3 => ?_) hn hcap hc40 hp48
    (by rw [hF1.accessible]; exact h.pacc) S hpc h0 h2 h1 h9 hsp h14 h5 hx15 hfs hdf hm
  have hF : MemFrame M S'.mem (R.rt ++ ws s p c) := hF1.trans hF3 fun a n ho => ⟨ho, by
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega⟩
  have hc41 : c < 2 ^ 41 := by omega
  have hpw' : p + 8 * wOf n ≤ 2 ^ 48 := by omega
  have hpa : S'.mem.accessible p (8 * wOf n) false = true := by
    rw [hF.accessible]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega))
  refine norm impl s S'.mem p c (wOf n) (natVal s.mem x xl % 2 ^ n) _ ?fin hcap hc41 hpw' hpa
    (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.lr) (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.fp)
    h.al h.sp0 h.sp1 (by rw [hF.accessible]; exact h.sacc) h.ra47 (wOf n) S' (Nat.le_refl _) hpc' h2' h0' h3'
    hsp' h14' h5' hx' hfs' hdf' rfl ?v
  case v =>
    rw [hv3, hval, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by unfold wOf; omega))]
  case fin =>
    intro s' n' hm' h0'' h1'' h2'' hfs'' hn' hv' hN
    refine h.post hk hF ?_ ?_ s' n' hm' h0'' h1'' h2'' hfs'' (by omega) hv' hN
    · refine hLF1.trans ⟨fun a k hin hout => hF3.readLE a k ?_⟩ fun _ _ hh => hh
      simp only [outside_cons, outside_nil, and_true] at hout ⊢; omega
    · refine RtInv.inv_frame' hF3 (fun r hr => ?_) hinv2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      have hsub : Held R L' (p + 8 * (wOf n - 1)) (p + 8 * wOf n - (p + 8 * (wOf n - 1))) :=
        h.pheld.sub (by omega) (by omega)
      dsimp only
      rcases hsub with hin | hout
      · exact Or.inr hin
      · exact Or.inl hout

end FvModexp.Amd64.Trunc
