import FvModexp.Proofs.Arm64.NatQ.MulLoopHead
import FvModexp.Proofs.Arm64.Nat.AddTo
import FvModexp.Proofs.Arm64.NatQ.MulCall
import FvModexp.Proofs.Arm64.NatQ.KSqrEndP
import FvModexp.Proofs.Arm64.NatQ.MulLoopCall

/-!
# [Q-form copy of Arm64/Nat/MulLoopAdd.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), chunk loop: `addTo(z[i:], t)` and back to the head (natmul.go:58)

From `LM` at `0x1bb264`: the bounds check `i ≤ m + n` (`BLS`, panic refuted), the spills of `t` (`176`, `112`, `104`),
`z[i:] = (p + 8i, m + n - i, c - i)` (slice mask), `addTo` (`AddTo.ens`) at `0x1bb1f0`, the reloads (`R3 = i + n`) and the
jump to the head `0x1bb204` ⟹ `LH` with `k + 1` chunks. `add_val`: the new value of `z[0:m+n]` (no wrap: the full product
fits).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep addToA
  addTo_entry stackBack_keep' tN')

/-- `addTo` as a summary in `LibMul.program` -/
theorem addSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibMul.program.link impl) addToA
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, xp, xl, xc] ∧
        (CallEnv R L s 4240 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4240 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4240 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8 ∧
          R.inv b L (s.regs 28).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        (natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ winA s 4240 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have hS := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc)
    (noExit_restrict hap AddTo.names) (codeIn_restrict_mono hap (IntAS.sub_of_all (ms := LibMul.names) (by decide)))
  rw [← LibMul.eq_only, addTo_entry] at hS
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
theorem mul_ra {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 321) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x1bae70 + 4 * i) := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg33)
    (show Extracted.seg33 ∈ Extracted.program.segments from
      List.getElem_mem (l := Extracted.program.segments) (n := 33) (by decide))
    (show ns.contains Extracted.seg33.name = false from hn) i
    (by simp [Extracted.seg33]; omega) (by simp [Extracted.seg33]; omega) (by decide)
  simpa [Extracted.seg33] using this

set_option maxRecDepth 20000 in
/-- `addTo(z[i:], t)`'s precondition at its entry (`SP - 256`) -/
theorem addPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent tp tc : Nat}
    {Mc : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mc)
    (ht : TOK R L1 Lk M Mc st tp tc) {i tl : Nat} (hi : i < xl) (htlc : tl ≤ tc) (htll : i + tl ≤ xl + yl)
    (S1 : State) (hsp : S1.sp.toNat = s.sp.toNat - 256) (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = Mc) :
    CallEnv R Lk S1 4240 48 ∧ tl ≤ xl + yl - i ∧ xl + yl - i ≤ c - i ∧ xl + yl - i < 2 ^ 40 ∧
      NatLive S1.mem R Lk (p + 8 * i) (xl + yl - i) ∧
      Outside (p + 8 * i) (8 * (xl + yl - i)) (win S1 4240 48) ∧ c - i < 2 ^ 63 ∧
      S1.mem.accessible tp (8 * tl) false = true ∧ tp + 8 * tl ≤ 2 ^ 48 ∧
      Held R Lk tp (8 * tl) ∧ Outside tp (8 * tl) (win S1 4240 48) ∧
      (0 < tl → Apart (p + 8 * i) (8 * (xl + yl - i)) tp (8 * tl)) ∧
      Apart (p + 8 * i) (8 * (xl + yl - i)) ((S1.regs 28).toNat + 16) 8 ∧
      R.inv bk Lk (S1.regs 28).toNat (view R.rt Lk S1.mem) := by
  obtain ⟨hW, hWs, -, -, -, -, -, hcap, hc40, hpw, -⟩ := h.lay
  have h40 := h.h40
  obtain ⟨htw, -, htp, -⟩ := h.tsep ht
  obtain ⟨ht0, -, htl, -⟩ := ht
  obtain ⟨-, hth, htacc, ht48⟩ := htl ht0
  obtain ⟨hp8, hph, hpacc, hp48⟩ := h.core.live (by omega)
  have hpg := h.core.pg (by omega)
  have hce := h.callee (S1 := S1) (stk1 := 4240) (above1 := 48) hsp hg hm (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hpw htw ⊢
  subst hm
  rw [hg, hsp]
  refine ⟨hce, by omega, by omega, by omega, fun _ => ⟨by omega, h.ext.held (hph.sub (by omega) (by omega)),
    by rw [h.fr.accessible]; exact Memory.accessible_sub _ hpacc (Or.inr rfl) (by omega) (by omega), by omega⟩,
    by omega, by omega,
    Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega), by omega,
    hth.sub (Nat.le_refl _) (by omega), by omega, fun _ => by unfold Apart at htp ⊢; omega,
    by unfold Apart at hpg ⊢; omega, h.inv⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the call `addTo(z[i:], t)`** (at its entry; `i = (k + 1)·n`): the continuation (at `0x1bb1f4`) gets `LB` (nothing
charged), `TOK`, the new value `z[0:m+n] = X[0:min(i+n, m)]·Y` and our slots -/
theorem ladd_call (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tl tc : Nat}
    {Mc : Memory} (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp xl yl (k + 1)) Mc)
    (ht : TOK R L1 Lk M Mc st tp tc) (hilt : (k + 1) * yl < xl) (htlc : tl ≤ tc) (htll : (k + 1) * yl + tl ≤ xl + yl)
    (htv : natVal Mc tp tl =
      natVal s.mem (xp + 8 * ((k + 1) * yl)) (min yl (xl - (k + 1) * yl)) * natVal s.mem yp yl)
    (hv : natVal Mc p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 addToA) (hsp : S1.sp.toNat = s.sp.toNat - 256)
    (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = Mc) (hra : S1.regs 30 = BitVec.ofNat 64 (0x1bae70 + 4 * 225))
    (r0 : S1.regs 0 = BitVec.ofNat 64 (p + 8 * ((k + 1) * yl))) (r1 : S1.regs 1 = BitVec.ofNat 64 (xl + yl - (k + 1) * yl))
    (r2 : S1.regs 2 = BitVec.ofNat 64 (c - (k + 1) * yl)) (r3 : S1.regs 3 = BitVec.ofNat 64 tp)
    (r4 : S1.regs 4 = BitVec.ofNat 64 tl) (r5 : S1.regs 5 = BitVec.ofNat 64 tc)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.pc = BitVec.ofNat 64 (0x1bae70 + 4 * 225) →
      (s2.sp = S1.sp ∧ s2.regs 28 = S1.regs 28 ∧ s2.regs 29 = S1.regs 29 ∧ s2.regs 18 = S1.regs 18) →
      ∀ (Lk' : List (Nat × Nat)) (bk' : Nat),
      LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (lsp xl yl (k + 1)) s2.mem →
      TOK R L1 Lk' M s2.mem st tp tc →
      natVal s2.mem p (xl + yl) = natVal s.mem xp (min ((k + 1 + 1) * yl) xl) * natVal s.mem yp yl →
      (∀ x m, s.sp.toNat - 168 ≤ x → x + m ≤ s.sp.toNat + 88 → s2.mem.readLE x m = Mc.readLE x m) →
      ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  obtain ⟨hW, hWs, -, -, hout, -, -, hcap, hc40, hpw, -⟩ := h.lay
  have h40 := h.h40
  have hP := addPre h ht hilt htlc htll S1 hsp hg hm
  obtain ⟨-, htp, -⟩ := h.tsep ht
  have hp48 := (h.core.live (by omega)).2.2.2
  have hst48 : tp + 8 * tc ≤ 2 ^ 48 := (ht.2.2.1 ht.1).2.2.2
  have b0 : p + 8 * ((k + 1) * yl) < 2 ^ 64 := by omega
  have b1' : xl + yl - (k + 1) * yl < 2 ^ 64 := by omega
  have b2 : c - (k + 1) * yl < 2 ^ 64 := by omega
  have b3 : tp < 2 ^ 64 := by omega
  have b4 : tl < 2 ^ 64 := by omega
  have b5 : tc < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (addSum impl hap R hmv bk Lk (BitVec.ofNat 64 (p + 8 * ((k + 1) * yl)))
    (BitVec.ofNat 64 (xl + yl - (k + 1) * yl)) (BitVec.ofNat 64 (c - (k + 1) * yl)) (BitVec.ofNat 64 tp)
    (BitVec.ofNat 64 tl) (BitVec.ofNat 64 tc)) hpc ⟨?_, ⟨r0, r1, r2, r3, r4, r5, trivial⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · rw [hra, tN' (by omega)]; exact mul_ra hap (by decide) 225 (by decide)
  · simp only [tN' b0, tN' b1', tN' b2, tN' b3, tN' b4, tN' b5]; exact hP
  · obtain ⟨hk, hval, Lk', bk', hext, hbud, hinv, hF, hLF⟩ := hq
    simp only [tN' b0, tN' b1', tN' b3, tN' b4] at hval hF hLF
    rw [hg] at hinv
    rw [hm] at hF hLF hreg hval
    simp only [winA, hsp] at hF
    have hF' : MemFrame Mc s2.mem (R.rt ++ [(s.sp.toNat - 256 - 4240, s.sp.toNat - 256 - 8),
        (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 48)] ++
        [(p + 8 * ((k + 1) * yl), p + 8 * ((k + 1) * yl) + 8 * (xl + yl - (k + 1) * yl))]) := hF
    have hcls : LCls R L1 M st p (xl + yl)
        [(p + 8 * ((k + 1) * yl), p + 8 * ((k + 1) * yl) + 8 * (xl + yl - (k + 1) * yl))] := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
    have hstw : Outside st 24 ([(s.sp.toNat - 256 - 4240, s.sp.toNat - 256 - 8),
        (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 48)] ++
        [(p + 8 * ((k + 1) * yl), p + 8 * ((k + 1) * yl) + 8 * (xl + yl - (k + 1) * yl))]) := by
      have hpst := h.core.pst (by omega)
      have hko := h.lwsOut _ (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨eW, -, -⟩ := h.hdrM
      simp only at hko
      unfold Apart at hpst
      simp only [outside_append, outside_cons, outside_nil, and_true]
      omega
    have hsbC : StackBackL R Lk Lk' st Mc s2.mem ∧ stCap s2.mem st = stCap Mc st := by
      refine NatSqr.stackBack_keepC h.sok (by rw [← List.append_assoc]; exact hF')
        (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) hstw hext
    have hsb := hsbC.1
    have hspk := h.spk
    have h' := h.step (k := 4240) (a := 48) (by omega) (by omega) hcls hF' hLF hreg hext (k' := 0)
      (Or.inr ⟨by omega, hsbC.2⟩) (by omega) hinv hsb
    simp only [Nat.add_zero] at h'
    have hkeep := h.calleeKeep (k := 4240) (a := 48) (by omega) (by omega) hcls hF'
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
    refine hK s2 (by rw [hr, hra]) hk Lk' bk' h' ht' ?_ fun x m h1 h2 => hkeep x m (by omega) h2 (Or.inr h1)
    rw [hval', show (k + 1) * yl + min yl (xl - (k + 1) * yl) = min ((k + 1 + 1) * yl) xl by
      rw [Nat.add_mul (k + 1) 1 yl, Nat.one_mul]; omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`addTo(z[i:], t)` and back to the head** -/
theorem ladd (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk k tp tl tc : Nat}
    (S : State) (hM : LM R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk k tp tl tc S)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (Lk' : List (Nat × Nat)) (bk' : Nat) (S' : State),
      LH R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (k + 1) tp tl tc S' →
      ReachesRet (LibMul.program.link impl) ret S' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have h := hM.lb
  obtain ⟨hW, hWs, hal, -, -, -, -, hcap, hc40, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have h40 := h.h40
  have hpc := hM.pc; have hsp := hM.sp; have h28 := hM.g; have h29 := hM.fp; have h18 := hM.x18
  have r0 := hM.r0; have r1 := hM.r1; have r2 := hM.r2
  have m128 := hM.m128; have m136 := hM.m136; have n120 := h.n120; have c96 := h.c96; have p144 := h.p144
  have hilt := hM.ilt
  obtain ⟨⟨-, ⟨-, -, ha0, hw0⟩, -⟩, -⟩ := h.core.pre
  have hsacc : S.mem.accessible (s.sp.toNat - 264) 352 true = true := by
    rw [h.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hm := maskN (i := (k + 1) * yl) (c := c) (by omega) (by omega)
  have htc := hM.tlc; have htll := hM.tll
  have hTo := hM.tok
  have hp48 := (h.core.live (by omega)).2.2.2
  have hst48 : tp + 8 * tc ≤ 2 ^ 48 := (hTo.2.2.1 hTo.1).2.2.2
  janus_run [m128, m136, n120, c96, p144, hm] until [addToA]
  refine ladd_call impl hap R hmv (h.local ?fr ?reg) (hTo.winKeep h ?frW) hilt htc htll ?htv ?hv _ rfl ?sp ?g rfl ?ra
    ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?cont
  case fr => janus_frame
  case frW => simp only [winA]; janus_frame
  case reg => janus_simp
  case htv => rw [(h.winVal hTo htc (by simp only [winA]; janus_frame)).2, hM.tv]
  case hv => rw [(h.winVal hTo htc (by simp only [winA]; janus_frame)).1, hM.val]
  case cont =>
    intro s2 hpc2 hk Lk' bk' hLB hT hval hkeep
    obtain ⟨k1, k2, k3, k4⟩ := hk
    simp only at k1 k2 k3 k4
    have e1 : s2.mem.readLE (s.sp.toNat - 120) 8 = (k + 1 + 1) * yl := by
      rw [hkeep _ _ (by omega) (by omega)]; janus_simp; rw [m136, Nat.add_mul (k + 1) 1 yl, Nat.one_mul]
    have e2 : s2.mem.readLE (s.sp.toNat - 144) 8 = tc := by rw [hkeep _ _ (by omega) (by omega)]; janus_simp
    have e3 : s2.mem.readLE (s.sp.toNat - 152) 8 = tl := by rw [hkeep _ _ (by omega) (by omega)]; janus_simp
    have e4 : s2.mem.readLE (s.sp.toNat - 80) 8 = tp := by rw [hkeep _ _ (by omega) (by omega)]; janus_simp
    have hacc2 : s2.mem.accessible (s.sp.toNat - 264) 352 true = true := by
      rw [hLB.frE.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
    clear hkeep
    janus_run [e1, e2, e3, e4] until [0x1bb204]
    refine hK Lk' bk' _ ⟨hLB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hilt, hT, hM.px, hM.py, hval⟩
    all_goals janus_simp
  all_goals try janus_simp
  all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

end FvModexp.Arm64.Q.NatMul
