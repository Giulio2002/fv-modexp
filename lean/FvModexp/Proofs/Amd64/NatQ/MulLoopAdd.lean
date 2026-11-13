import FvModexp.Proofs.Amd64.NatQ.MulLoopCall
import FvModexp.Proofs.Amd64.NatQ.MulLoopNatC
import FvModexp.Proofs.Amd64.Nat.AddTo

/-!
# [amd64 port (divmc s46) of the Q-form Arm64/NatQ/MulLoopAdd.lean — TIGHT COSTS] `nat.mul` (amd64), chunk loop: `addTo(z[i:], t)` and back to the head (natmul.go:58)

From `LM` at `0x5f0de5`: the bounds check `i ≤ m + n` (`JBE 0x5f0ccb`; the panic `0x5f0ea8` refuted), the spills of
`t` (`0xb0, 0x68, 0x60(SP')` = `RSP - 80, - 152, - 160`), `z[i:] = (p + 8i, m + n - i, c - i)` (slice mask), `addTo`
(`AddTo.ens`) at `0x5e62c0` (entered at `RSP - 264`, return `0x5f0d1f`), the reloads (`DX = i + n`, `t`) and the head
`0x5f0d39` ⟹ `LH` with `k + 1` chunks. `add_val`: the new value of `z[0:m+n]` (no wrap: the full product fits).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep
  stackBack_keep')

abbrev addToM : Nat := 0x5e62c0

theorem addTo_entryM : segAddr Extracted.program AddTo.fn = addToM := by decide

/-- `addTo` as a summary in `LibMul.program` -/
theorem addSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibMul.program.link impl) addToM
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [zp, zl, zc, xp, xl, xc] ∧ s.df = false ∧
        (CallEnv R L s 4232 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4232 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4232 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 14).toNat + 16) 8 ∧ Apart zp.toNat (8 * zl.toNat) (s.fsBase.toNat - 8) 8 ∧
          R.inv b L (s.regs 14).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        (s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ win s 4232 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have hS := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc)
    (A64.noExit_restrict64 hap AddTo.names) (by simp [numIntRegs])
    (A64.codeIn_restrict_mono64 hap (IntAS.sub_of_all (ms := LibMul.names) (by decide)))
  rw [← LibMul.eq_only, addTo_entryM] at hS
  exact hS

/-- **the value after `addTo(z[i:], t)`** (`N = m + n`, `z[0:N] = X[0:i]·Y` before, `t = X[i:i+cc]·Y`) -/
theorem add_val {Mc A m0 : Memory} {p xp i cc N T Y : Nat} (hcN : i + cc + (N - (i + cc)) = N) (hiN : i ≤ N)
    (hY : Y < 2 ^ (64 * (N - (i + cc))))
    (hlo : natVal A p i = natVal Mc p i)
    (hhi : natVal A (p + 8 * i) (N - i) = (natVal Mc (p + 8 * i) (N - i) + T) % 2 ^ (64 * (N - i)))
    (hv : natVal Mc p N = natVal m0 xp i * Y) (hT : T = natVal m0 (xp + 8 * i) cc * Y) :
    natVal A p N = natVal m0 xp (i + cc) * Y := by
  have eA := natVal_add A p i (N - i)
  have eM := natVal_add Mc p i (N - i)
  have eX := natVal_add m0 xp i cc
  rw [show i + (N - i) = N by omega] at eA eM
  have hlt : (natVal m0 xp i + 2 ^ (64 * i) * natVal m0 (xp + 8 * i) cc) * Y < 2 ^ (64 * (i + (N - i))) := by
    rw [← eX]
    have h1 := natVal_lt m0 xp (i + cc)
    have h2 : natVal m0 xp (i + cc) * Y < 2 ^ (64 * (i + cc)) * 2 ^ (64 * (N - (i + cc))) :=
      Nat.mul_lt_mul_of_lt_of_lt h1 hY
    rw [← Nat.pow_add, show 64 * (i + cc) + 64 * (N - (i + cc)) = 64 * (i + (N - i)) by omega] at h2
    exact h2
  have := chunk_val (natVal Mc p i) (natVal Mc (p + 8 * i) (N - i)) T (natVal m0 xp i)
    (natVal m0 (xp + 8 * i) cc) Y i (N - i) (by rw [← eM, hv]) hlt hT
  rw [eA, hlo, hhi, this, ← eX]

set_option maxRecDepth 20000 in
/-- `addTo(z[i:], t)`'s precondition at its entry (`RSP - 264`) -/
theorem addPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent tp tc : Nat}
    {Mc : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mc)
    (ht : TOK R L1 Lk M Mc st tp tc) {i tl : Nat} (hi : i < xl) (htlc : tl ≤ tc) (htll : i + tl ≤ xl + yl)
    (S1 : State) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = Mc)
    (hfs : S1.fsBase = s.fsBase) :
    CallEnv R Lk S1 4232 48 ∧ tl ≤ xl + yl - i ∧ xl + yl - i ≤ c - i ∧ xl + yl - i < 2 ^ 40 ∧
      NatLive S1.mem R Lk (p + 8 * i) (xl + yl - i) ∧
      Outside (p + 8 * i) (8 * (xl + yl - i)) (win S1 4232 48) ∧ c - i < 2 ^ 63 ∧
      S1.mem.accessible tp (8 * tl) false = true ∧ tp + 8 * tl ≤ 2 ^ 48 ∧
      Held R Lk tp (8 * tl) ∧ Outside tp (8 * tl) (win S1 4232 48) ∧
      (0 < tl → Apart (p + 8 * i) (8 * (xl + yl - i)) tp (8 * tl)) ∧
      Apart (p + 8 * i) (8 * (xl + yl - i)) ((S1.regs 14).toNat + 16) 8 ∧
      Apart (p + 8 * i) (8 * (xl + yl - i)) (S1.fsBase.toNat - 8) 8 ∧
      R.inv bk Lk (S1.regs 14).toNat (view R.rt Lk S1.mem) := by
  obtain ⟨hW, hWs, -, -, -, -, -, hcap, hc40, hpw, -⟩ := h.lay
  have h40 := h.h40
  obtain ⟨htw, -, htp, -⟩ := h.tsep ht
  obtain ⟨ht0, -, htl, -⟩ := ht
  obtain ⟨-, hth, htacc, ht48⟩ := htl ht0
  obtain ⟨hp8, hph, hpacc, hp48⟩ := h.core.live (by omega)
  have hpg := h.core.pg (by omega)
  have hpt := h.core.ptls (by omega)
  have hce := h.callee (S1 := S1) (stk1 := 4232) (above1 := 48) hsp hg hm hfs (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hpw htw ⊢
  simp only [NatSqr.tls] at hpt
  subst hm
  rw [hg, hsp, hfs]
  refine ⟨hce, by omega, by omega, by omega, fun _ => ⟨by omega, h.ext.held (hph.sub (by omega) (by omega)),
    by rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inr rfl) (by omega) (by omega), by omega⟩,
    by omega, by omega,
    Janus.Arm64.Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega), by omega,
    hth.sub (Nat.le_refl _) (by omega), by omega, fun _ => by unfold Apart at htp ⊢; omega,
    by unfold Apart at hpg ⊢; omega, by unfold Apart at hpt ⊢; omega, h.inv⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the call `addTo(z[i:], t)`** (at its entry `RSP - 264`; `i = (k + 1)·n`): the continuation (at `0x5f0d1f`) gets
`LB` (nothing charged), `TOK`, the new value `z[0:m+n] = X[0:min(i+n, m)]·Y` and our slots -/
theorem ladd_call (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tl tc : Nat}
    {Mc : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp xl yl (k + 1)) Mc)
    (ht : TOK R L1 Lk M Mc st tp tc) (hilt : (k + 1) * yl < xl) (htlc : tl ≤ tc) (htll : (k + 1) * yl + tl ≤ xl + yl)
    (htv : natVal Mc tp tl =
      natVal s.mem (xp + 8 * ((k + 1) * yl)) (min yl (xl - (k + 1) * yl)) * natVal s.mem yp yl)
    (hv : natVal Mc p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 addToM) (hsp : S1.regs 4 = s.regs 4 - 264#64)
    (hg : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx15 : S1.xmm 15 = s.xmm 15) (hm : S1.mem = Mc)
    (hra : Mc.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0840 + 1247)
    (r0 : S1.regs 0 = BitVec.ofNat 64 (p + 8 * ((k + 1) * yl))) (r3 : S1.regs 3 = BitVec.ofNat 64 (xl + yl - (k + 1) * yl))
    (r1 : S1.regs 1 = BitVec.ofNat 64 (c - (k + 1) * yl)) (r7 : S1.regs 7 = BitVec.ofNat 64 tp)
    (r6 : S1.regs 6 = BitVec.ofNat 64 tl) (r8 : S1.regs 8 = BitVec.ofNat 64 tc)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.rip = BitVec.ofNat 64 (0x5f0840 + 1247) → s2.regs 4 = s.regs 4 - 256#64 →
      s2.regs 14 = s.regs 14 → s2.regs 5 = s.regs 4 - 8#64 → s2.fsBase = s.fsBase → s2.df = s.df →
      s2.xmm 15 = s.xmm 15 →
      ∀ (Lk' : List (Nat × Nat)) (bk' : Nat),
      LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (lsp xl yl (k + 1)) s2.mem →
      TOK R L1 Lk' M s2.mem st tp tc →
      natVal s2.mem p (xl + yl) = natVal s.mem xp (min ((k + 1 + 1) * yl) xl) * natVal s.mem yp yl →
      (∀ x m, (s.regs 4).toNat - 176 ≤ x → x + m ≤ (s.regs 4).toNat + 88 → s2.mem.readLE x m = Mc.readLE x m) →
      ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  obtain ⟨hW, hWs, -, -, hout, -, -, hcap, hc40, hpw, -⟩ := h.lay
  have h40 := h.h40
  have hsp' : (S1.regs 4).toNat = (s.regs 4).toNat - 264 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hP := addPre h ht hilt htlc htll S1 hsp' hg hm hfs
  obtain ⟨-, htp, -⟩ := h.tsep ht
  have hp48 := (h.core.live (by omega)).2.2.2
  have hst48 : tp + 8 * tc ≤ 2 ^ 48 := (ht.2.2.1 ht.1).2.2.2
  have b0 : p + 8 * ((k + 1) * yl) < 2 ^ 64 := by omega
  have b1' : xl + yl - (k + 1) * yl < 2 ^ 64 := by omega
  have b2 : c - (k + 1) * yl < 2 ^ 64 := by omega
  have b3 : tp < 2 ^ 64 := by omega
  have b4 : tl < 2 ^ 64 := by omega
  have b5 : tc < 2 ^ 64 := by omega
  have tN : ∀ {v : Nat}, v < 2 ^ 64 → (BitVec.ofNat 64 v).toNat = v := fun h => by
    simp only [BitVec.toNat_ofNat]; omega
  have hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f0840 + 1247 := by rw [hm, hsp', hra]
  refine ReachesRet.call_regions (addSum impl hap R hmv bk Lk (BitVec.ofNat 64 (p + 8 * ((k + 1) * yl)))
    (BitVec.ofNat 64 (xl + yl - (k + 1) * yl)) (BitVec.ofNat 64 (c - (k + 1) * yl)) (BitVec.ofNat 64 tp)
    (BitVec.ofNat 64 tl) (BitVec.ofNat 64 tc)) hpc ⟨?_, hx15.trans hx150,
      by simp [ArgsFrom64, argReg, intArgRegs, r0, r3, r1, r7, r6, r8], hdf.trans hdf0, ?_⟩ fun s2 hr hq hreg => ?_
  · simp only [regSP]; rw [hrd]; exact ra_mul hap (by decide) 1247 (by decide)
  · simp only [tN b0, tN b1', tN b2, tN b3, tN b4]; exact hP
  · obtain ⟨⟨k4, k5, k14, k15⟩, efs, edf, hval, Lk', bk', hext, hbud, hinv, hF, hLF⟩ := hq
    simp only [tN b0, tN b1', tN b3, tN b4] at hval hF hLF
    rw [hg] at hinv
    rw [hm] at hF hLF hreg hval
    simp only [win, hsp'] at hF
    have hF' : MemFrame Mc s2.mem (R.rt ++ [((s.regs 4).toNat - 264 - 4232, (s.regs 4).toNat - 264 + 48)] ++
        [(p + 8 * ((k + 1) * yl), p + 8 * ((k + 1) * yl) + 8 * (xl + yl - (k + 1) * yl))]) := hF
    have hcls : LCls R L1 M st p (xl + yl)
        [(p + 8 * ((k + 1) * yl), p + 8 * ((k + 1) * yl) + 8 * (xl + yl - (k + 1) * yl))] := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
    have hstw : Outside st 24 ([((s.regs 4).toNat - 264 - 4232, (s.regs 4).toNat - 264 + 48)] ++
        [(p + 8 * ((k + 1) * yl), p + 8 * ((k + 1) * yl) + 8 * (xl + yl - (k + 1) * yl))]) := by
      have hpst := h.core.pst (by omega)
      have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only at hko
      unfold Apart at hpst
      simp only [outside_append, outside_cons, outside_nil, and_true]
      omega
    have hsbC : StackBackL R Lk Lk' st Mc s2.mem ∧ stCap s2.mem st = stCap Mc st := by
      refine NatSqr.stackBack_keepC h.sok (by rw [← List.append_assoc]; exact hF')
        (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) hstw hext
    have hsb := hsbC.1
    have hspk := h.spk
    have h' := h.step (k := 4232) (a := 48) (by omega) (by omega) hcls hF' hLF hreg hext (k' := 0)
      (Or.inr ⟨by omega, hsbC.2⟩) (by omega) hinv hsb
    simp only [Nat.add_zero] at h'
    have hkeep := h.calleeKeep (k := 4232) (a := 48) (by omega) (by omega) hcls hF'
    have ht' : TOK R L1 Lk' M s2.mem st tp tc := by
      refine TOK.after h ht h' hsb.1 hext ht.2.1 (fun hc => ?_) (Or.inl ⟨rfl, rfl⟩)
      obtain ⟨a1, a2, a3, a4⟩ := ht.2.2.1 hc
      exact ⟨a1, hext.held a2, by rw [hF.accessible]; exact a3, a4⟩
    have hlo : natVal s2.mem p ((k + 1) * yl) = natVal Mc p ((k + 1) * yl) := by
      have hpH : Held R Lk p (8 * ((k + 1) * yl)) :=
        (h.ext.held (h.core.live (by omega)).2.1).sub (Nat.le_refl _) (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at hpw
      unfold natVal
      refine Held.readLE2 hpH hF' hLF ?_ ?_
      · simp only [outside_cons, outside_nil, and_true]; omega
      · simp only [outside_cons, outside_nil, and_true]; omega
    have hval' := add_val (Mc := Mc) (A := s2.mem) (m0 := s.mem) (p := p) (xp := xp) (i := (k + 1) * yl)
      (cc := min yl (xl - (k + 1) * yl)) (N := xl + yl) (T := natVal Mc tp tl) (Y := natVal s.mem yp yl)
      (by omega) (by omega) (Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.pow_le_pow_right (by omega) (by omega)))
      hlo hval hv htv
    have hsp2 : s2.regs 4 = s.regs 4 - 256#64 := by
      rw [k4, hsp]; apply BitVec.eq_of_toNat_eq
      have e8 : (8 : BitVec 64).toNat = 8 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8]; omega
    refine hK s2 (by rw [hr, retAddrOf, hrd]) hsp2 (k14.trans hg) (k5.trans h5) (efs.trans hfs) (edf.trans hdf)
      (k15.trans hx15) Lk' bk' h' ht' ?_ fun x m h1 h2 => hkeep x m h1 h2
    rw [hval', show (k + 1) * yl + min yl (xl - (k + 1) * yl) = min ((k + 1 + 1) * yl) xl by
      rw [Nat.add_mul (k + 1) 1 yl, Nat.one_mul]; omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`addTo(z[i:], t)` and back to the head** -/
theorem ladd (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tl tc : Nat}
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S : State) (hM : LM R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' : Nat) (S' : State),
      LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (k + 1) tp tl tc S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have h := hM.lb
  obtain ⟨hW, hWs, hal, ha48, -, -, -, hcap, hc40, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have h40 := h.h40
  have hpc := hM.pc; have hsp := hM.sp; have h14 := hM.g; have h5 := hM.bp
  have r0 := hM.r0; have r1 := hM.r1; have r3 := hM.r3
  have m78 := hM.m78; have m80 := hM.m80; have m88 := hM.m88; have n70 := h.n70; have c58 := h.c58
  have p90 := h.p90
  have hilt := hM.ilt
  obtain ⟨⟨-, ⟨-, -, hw0⟩, -⟩, -⟩ := h.core.pre
  simp only [regSP] at hw0
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 264) 352 true = true := by
    rw [h.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 256 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have htc := hM.tlc; have htll := hM.tll
  have hTo := hM.tok
  have hp48 := (h.core.live (by omega)).2.2.2
  have hst48 : tp + 8 * tc ≤ 2 ^ 48 := (hTo.2.2.1 hTo.1).2.2.2
  have hsc : BitVec.ofNat 64 c - BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 (c - (k + 1) * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsn : BitVec.ofNat 64 (xl + yl) - BitVec.ofNat 64 ((k + 1) * yl) = BitVec.ofNat 64 (xl + yl - (k + 1) * yl) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hm : ((0#64 - BitVec.ofNat 64 (c - (k + 1) * yl)).sshiftRight 63 &&& BitVec.ofNat 64 (8 * ((k + 1) * yl))) =
      BitVec.ofNat 64 (8 * ((k + 1) * yl)) :=
    neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have hm' : (BitVec.ofNat 64 (8 * ((k + 1) * yl)) &&& (0#64 - BitVec.ofNat 64 (c - (k + 1) * yl)).sshiftRight 63) =
      BitVec.ofNat 64 (8 * ((k + 1) * yl)) := by rw [BitVec.and_comm]; exact hm
  have hpa : BitVec.ofNat 64 (8 * ((k + 1) * yl)) + BitVec.ofNat 64 p = BitVec.ofNat 64 (p + 8 * ((k + 1) * yl)) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  janus64_run [m78, m80, n70, c58, p90, hsp', hsc, hsn, hm, hm', hpa, BitVec.msb_eq_decide] until [addToM]
  refine ladd_call impl hap R hmv (h.localP ?fr ?reg) (hTo.winKeep h ?frW) hilt htc htll ?htv ?hv hx150 hdf0 _ rfl
    ?sp ?g ?bp ?fs ?df ?x15 rfl ?ra ?r0 ?r3 ?r1 ?r7 ?r6 ?r8 ?cont
  case fr => janus_frame
  case frW => simp only [win]; janus_frame
  case htv => rw [(h.winVal hTo htc (by simp only [win]; janus_frame)).2, hM.tv]
  case hv => rw [(h.winVal hTo htc (by simp only [win]; janus_frame)).1, hM.val]
  case cont =>
    intro s2 hpc2 hsp2 hg2 hbp2 hfs2 hdf2 hx2 Lk' bk' hLB hT hval hkeep
    have e1 : s2.mem.readLE ((s.regs 4).toNat - 120) 8 = (k + 1 + 1) * yl := by
      rw [hkeep _ _ (by omega) (by omega)]; janus64_simp; rw [Nat.add_mul (k + 1) 1 yl, Nat.one_mul]
    have e2 : s2.mem.readLE ((s.regs 4).toNat - 152) 8 = tc := by rw [hkeep _ _ (by omega) (by omega)]; janus64_simp
    have e3 : s2.mem.readLE ((s.regs 4).toNat - 160) 8 = tl := by rw [hkeep _ _ (by omega) (by omega)]; janus64_simp
    have e4 : s2.mem.readLE ((s.regs 4).toNat - 80) 8 = tp := by rw [hkeep _ _ (by omega) (by omega)]; janus64_simp
    have hacc2 : s2.mem.accessible ((s.regs 4).toNat - 264) 352 true = true := by
      rw [hLB.frE.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
    have hsp2' : (s2.regs 4).toNat = (s.regs 4).toNat - 256 := by
      rw [hsp2]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    clear hkeep
    janus64_run [e1, e2, e3, e4, hsp2'] until [0x5f0d39]
    refine hK Lk' bk' _ ⟨hLB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hilt, hT, hM.px, hM.py, hval⟩
    all_goals try janus64_simp
    all_goals first
      | exact hfs2
      | exact hdf2
      | exact hx2
      | fail "SHOW"
  all_goals try janus64_simp
  all_goals first
    | exact hM.fs
    | exact hM.df
    | exact hM.x15
    | exact hM.df.trans hdf0
    | exact hM.x15.trans hx150
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | fail "SHOW"

end FvModexp.Amd64.Q.NatMul
