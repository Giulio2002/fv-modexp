import FvModexp.Proofs.Amd64.Nat.LshDefs
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.DivmcNat

/-!
# `nat.lsh` (amd64): `clear(z[0 : n-m])` (`+0x2d2`), the inlined `z.norm()` loop (`+0x304`) and the return

At `hClr` (`CMPQ CX, BX`): `AX = p`, `CX = c`, `DX = n + 1`, `BX = s / 64`; `z[n-m : n+1]` holds `X · 2^(s % 64)`.
`TESTQ BX; JE` skips the clear; else `memclrNoHeapPointers(p, 8 (s/64))` (`+0x2e0`), reloads `AX, CX, DX` from
`e - 24, e - 80, e - 56`. Norm loop head `+0x304` (`TESTQ DX, DX; JLE`; `MOVQ -8(AX)(DX*8), SI; TESTQ SI; JE +0x301`
(`DECQ DX`)); `CMPQ DX, CX; JA panic; MOVQ DX, BX; ADDQ $0x88, SP; POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (natVal_drop_zero)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Lsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Amd64.Segment) (s : State) (M : Janus.Arm64.Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c → s'.fsBase = s.fsBase → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 4248 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 64 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hNorm → S.regs 2 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 1 = BitVec.ofNat 64 c → S.regs 4 = s.regs 4 - 144#64 →
      S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase →
      S.df = false → S.mem = M → natVal M p i = V →
      ReachesRet (LibLsh.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Q s' := by
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

/-- `z[0 : q]` zero below `X · 2^r` at `q` gives `X · 2^(64 q + r)` -/
theorem val_clr (m : Janus.Arm64.Memory) (p q xl X r : Nat) (h0 : m.readLE p (8 * q) = 0)
    (h1 : natVal m (p + 8 * q) (xl + 1) = X * 2 ^ r) :
    natVal m p (xl + q + 1) = X * 2 ^ (64 * q + r) := by
  rw [show xl + q + 1 = q + (xl + 1) by omega, natVal_add, h1]
  simp only [natVal] at h0 ⊢
  rw [h0, Nat.zero_add, Nat.pow_add]; ac_rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the clear point (memory `M2` after the shifted copy and `z[n]`) to the return, with the postcondition -/
theorem fromClr (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (M2 : Janus.Arm64.Memory) (hF1 : MemFrame M M2 (R.rt ++ ws s p c)) (hLF1 : LiveFrame M M2 L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' M2))
    (hval : natVal M2 (p + 8 * (sh / 64)) (xl + 1) = natVal s.mem x xl * 2 ^ (sh % 64))
    (r24 : M2.readLE ((s.regs 4).toNat - 24) 8 = p) (r56 : M2.readLE ((s.regs 4).toNat - 56) 8 = need xl sh)
    (r80 : M2.readLE ((s.regs 4).toNat - 80) 8 = c)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hClr) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h2 : S.regs 2 = BitVec.ofNat 64 (need xl sh))
    (h3 : S.regs 3 = BitVec.ofNat 64 (sh / 64))
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M2) :
    ReachesRet (LibLsh.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hal := h.al; have hwrt := h.wrt; have hra := h.ra47
  have hpw := h.pw; have hgw := h.gw
  simp only [need] at hcap hn16 r56 h2
  unfold Apart at hpw hgw
  have hws : ∀ a n, ((s.regs 4).toNat - 8 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 8) → Outside a n (R.rt ++ ws s p c) := by
    intro a n ha
    simp only [ws, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h.wrt.of_sub (by omega) (by omega), by omega, by omega⟩
  have r1 : M2.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.lr
  have r2 : M2.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.fp
  have hsacc : M2.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true := by rw [hF1.accessible]; exact h.sacc
  have hpacc : M2.accessible p (8 * c) true = true := by rw [hF1.accessible]; exact h.pacc
  have hc41 : c < 2 ^ 41 := by omega
  have hcm : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hshv : 64 * (sh / 64) + sh % 64 = sh := by omega
  -- the final step: norm from `i = n + 1` and the postcondition
  have fin : ∀ (m : Janus.Arm64.Memory) (S' : State), MemFrame M m (R.rt ++ ws s p c) →
      LiveFrame M m L' [(p, p + 8 * c)] →
      R.inv b' L' (s.regs 14).toNat (view R.rt L' m) → natVal m p (xl + sh / 64 + 1) = natVal s.mem x xl * 2 ^ sh →
      S'.rip = BitVec.ofNat 64 hNorm → S'.regs 2 = BitVec.ofNat 64 (xl + sh / 64 + 1) →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 1 = BitVec.ofNat 64 c → S'.regs 4 = s.regs 4 - 144#64 →
      S'.regs 14 = s.regs 14 → S'.regs 5 = s.regs 4 - 8#64 → S'.xmm 15 = s.xmm 15 → S'.fsBase = s.fsBase →
      S'.df = false → S'.mem = m →
      ReachesRet (LibLsh.program.link impl) (retAddrOf s) S' fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl sh s s' := by
    intro m S' hF hLF hinv hv hpc' h2' h0' h1' hsp' h14' h5' hx' hfs' hdf' hm'
    refine norm impl s m p c (xl + sh / 64 + 1) (natVal s.mem x xl * 2 ^ sh) _ ?_ hcap hc41 (by omega)
      (by
        rw [hF.accessible]
        exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)))
      (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.lr) (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.fp)
      hal hsp0 hsp1 (by rw [hF.accessible]; exact h.sacc) hra _ S' (Nat.le_refl _) hpc' h2' h0' h1' hsp' h14'
      h5' hx' hfs' hdf' hm' hv
    intro s' n' hm'' h0'' h1'' h2'' hfs'' hn' hv' hN
    exact h.post hF hLF hinv s' n' hm'' h0'' h1'' h2'' hfs'' (by omega) hv' hN
  by_cases hq0 : sh / 64 = 0
  · have hq0' : BitVec.ofNat 64 (sh / 64) = 0#64 := by rw [hq0]
    rw [hq0'] at h3
    janus64_run [hm, hcm, BitVec.msb_eq_decide] until [hNorm]
    refine fin M2 _ hF1 hLF1 hinv2 ?v ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case v =>
      have := val_clr M2 p (sh / 64) xl (natVal s.mem x xl) (sh % 64) (by rw [hq0]; rfl) hval
      rwa [hshv] at this
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hfs | exact hdf
  · have hLs := h.lsep
    simp only [LiveSep, win] at hLs
    have hph : Held R L' p (8 * (sh / 64)) := h.pheld.sub (Nat.le_refl _) (by omega)
    have hph' : InRanges p (8 * (sh / 64)) L' ∨ Outside p (8 * (sh / 64)) R.rt := hph
    have hok : R.ok (cA "runtime.memclrNoHeapPointers") [p, sh / 64 * 8] := h.sv.2.2.1 _ _ (by omega)
    have hph2 : InRanges p (sh / 64 * 8) L' ∨ Outside p (sh / 64 * 8) R.rt := by
      rw [show sh / 64 * 8 = 8 * (sh / 64) by omega]; exact hph'
    have hx0 := h.x15
    have hpacc' : M2.accessible p (8 * (sh / 64)) true = true :=
      Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)
    have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
    have hgacc : M2.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hF1.accessible]; exact h.gacc
    have hpg := h.pg; have hpf := h.pf; have htw := h.tw
    unfold Apart at hpg hpf htw
    have hgQ : M2.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      rw [hF1.readLE _ _ (by
        simp only [ws, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h.grt, by omega, by omega⟩), h.grd]
    have hgok := h.gok
    have htacc : M2.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hF1.accessible]; exact h.tacc
    have htls : M2.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
      rw [hF1.readLE _ _ (by
        simp only [ws, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨h.trt, by omega, by omega⟩), h.tls]
    have htb := h.tlsg.base; have htrt := h.trt
    have hq8 : 8 * (sh / 64) % 18446744073709551616 = 8 * (sh / 64) := Nat.mod_eq_of_lt (by omega)
    have hq0'' : (BitVec.ofNat 64 (sh / 64) = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    janus64_run [hm, hcm, hq8, hq0'', r24, r56, r80, r1, r2, hgQ, hfs, BitVec.msb_eq_decide] until [hNorm]
      calls [hmc L' b']
    rename_i _ _ _ m _ _ hF2 hLF2 hinv3 hz
    have hz' := Expmc.readLE_zeroed hz
    rw [show sh / 64 * 8 = 8 * (sh / 64) by omega] at hz'
    have hP : ∀ v, MemFrame M2 (M2.writeLE ((s.regs 4).toNat - 152) 8 v)
        [((s.regs 4).toNat - 152, (s.regs 4).toNat - 152 + 8)] := fun v => by janus_frame
    have hF12q : MemFrame M2 m (R.rt ++ [((s.regs 4).toNat - 4248, (s.regs 4).toNat - 8), (p, p + sh / 64 * 8)]) :=
      (hP _).trans hF2 fun a k ho => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        obtain ⟨hr, h1', h2'⟩ := ho
        exact ⟨by omega, ⟨hr, by omega, by omega⟩, by omega⟩
    have hF12 : MemFrame M2 m (R.rt ++ ws s p c) := hF12q.mono fun a k ho => by
      simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2'⟩ := ho
      exact ⟨hr, h1', by omega⟩
    have hLF12q : LiveFrame M2 m L' [(p, p + sh / 64 * 8)] := ⟨fun a k hin ho => by
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this ho
      rw [hLF2.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
        (hP _).readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]⟩
    have hLF12 : LiveFrame M2 m L' [(p, p + 8 * c)] := ⟨fun a k hin ho => hLF12q.readLE a k hin (by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)⟩
    refine fin m _ (hF1.trans hF12 fun a k ho => ⟨ho, ho⟩) (hLF1.trans hLF12 fun _ _ hh => hh) hinv3 ?v
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case v =>
      have hh : Held R L' (p + 8 * (sh / 64)) (8 * (xl + 1)) := h.pheld.sub (by omega) (by omega)
      have h1v : m.readLE (p + 8 * (sh / 64)) (8 * (xl + 1)) = M2.readLE (p + 8 * (sh / 64)) (8 * (xl + 1)) := by
        rcases hh with hin | hout
        · exact hLF12q.readLE _ _ hin (by simp only [outside_cons, outside_nil, and_true]; omega)
        · exact hF12q.readLE _ _ (by
            simp only [outside_append, outside_cons, outside_nil, and_true]
            exact ⟨hout, by omega, by omega⟩)
      have := val_clr m p (sh / 64) xl (natVal s.mem x xl) (sh % 64) hz' (by
        simp only [natVal] at hval ⊢; rw [h1v]; exact hval)
      rwa [hshv] at this
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hfs | exact hdf

end FvModexp.Amd64.Lsh
