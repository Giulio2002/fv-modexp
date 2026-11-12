import FvModexp.Proofs.Arm64.Nat.MulLoopPA
import FvModexp.Proofs.Arm64.Nat.MulLoopAdd
import FvModexp.Proofs.Arm64.Nat.StackNat

/-!
# `nat.mul` (arm64), the chunk loop's prologue: `t := stk.nat(2n)` (natmul.go:55) → the loop head with `k = 0`

`lbOf` (pure): `LB` (spent `lsp ℓ n 0`), `TOK` for `t` and the value from `LP` at the call and `StackNat.PostL`.
`lnat`: the call (`StackNat.sumL` in `LibMul`), the return `0x1bb0c0` (`R3 = n`, `JMP` head) ⟹ `LH … 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep tN')

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`LB`, `TOK` and the value after `t := stk.nat(2n)`** -/
theorem lbOf {P S : State} (h : LP R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P)
    (hreg : S.mem.regions = P.mem.regions) (hq : StackNat.PostL R bk Lk 4208 24 st (2 * yl) P S) :
    ∃ (Lk' : List (Nat × Nat)) (bk' : Nat),
      LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (lsp (stLen M st) yl 0) S.mem ∧
      TOK R L1 Lk' M S.mem st (stW S.mem st + 8 * stLen M st) (2 * yl) ∧
      S.regs 0 = BitVec.ofNat 64 (stW S.mem st + 8 * stLen M st) ∧ S.regs 1 = BitVec.ofNat 64 (2 * yl) ∧
      S.regs 2 = BitVec.ofNat 64 (2 * yl) ∧
      natVal S.mem p (xl + yl) = natVal s.mem xp yl * natVal s.mem yp yl := by
  have hq0 := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, hc40, hpw, hx12, hy12, -⟩ := hq0.lay
  have h40 := hq0.h40
  obtain ⟨eW, eL, eC⟩ := hq0.hdrM
  obtain ⟨⟨-, hlenP, harrP⟩, hmemP⟩ := hq0.sb
  obtain ⟨hr0, hr1, hr2, Lk', bk', ⟨hext, hbud, hinv⟩, hok, hlen, hsame, hgrow, hF, hLF, hmem⟩ := hq
  have hspP : P.sp.toNat = s.sp.toNat - 256 := by rw [h.sp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsp : StkPre R L s W 88 st := hq0.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, hsth, -, -, -, -, -⟩, hstw, -, -, -, hfw, -, -, -, -, hfgA⟩ := hsp
  have hgrt : Outside RunIface.gA 32 R.rt := hq0.core.pre.2.2.2.1.2.2.2.2.2.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfw hfgA hpw
  have hlcP := hq0.sok.2.2.2.2.2.1
  have hkT : 0 < 2 * yl := by omega
  have hscr := Scr.of_post (m0 := P.mem) (k := 2 * yl) hok hlen hkT hsame hgrow rfl
  rw [hlenP] at hscr hlen hbud
  rw [hlenP] at hr0
  -- the stack array at `P`: `M`'s or fresh
  have hstkP := hq0.stk
  -- the callee's writes are classified
  have hcls : LCls R L1 M st p (xl + yl) (stkWs P.mem st) := hq0.stkCls
  have hF' : MemFrame P.mem S.mem (R.rt ++ [(s.sp.toNat - 256 - 4208, s.sp.toNat - 256 - 8),
      (s.sp.toNat - 256 + 8, s.sp.toNat - 256 + 24)] ++ stkWs P.mem st) := by
    have := hF; simp only [winA, hspP] at this; exact this
  obtain ⟨hfr, hlf⟩ := hq0.frames (k := 4208) (a := 24) (by omega) (by omega) hcls hF' hLF
  -- frame words
  have hko := hq0.lwsOut
  have hrd : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat + 88 → (x + m ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 232 ≤ x) →
      S.mem.readLE x m = P.mem.readLE x m := by
    intro x m h1 h2 h3
    refine hF'.readLE _ _ ?_
    rw [outside_append, outside_append]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩,
      outside_of_forall fun r hr => ?_⟩
    obtain ⟨hle, hc⟩ := hq0.cls hcls r hr
    rcases hc with ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · have := hko q hq; omega
    · have := NatSub.outside_of_inRanges (hout.of_sub (a := x) (n := m) (by omega) (by omega)) hin; omega
  -- `t`
  have hscrL : Scr R Lk Lk' P.mem S.mem st (stW S.mem st + 8 * stLen M st) (2 * yl) := hscr
  have hloc : (stW M st + 8 * stLen M st ≤ stW S.mem st + 8 * stLen M st ∧
      stW S.mem st + 8 * stLen M st + 8 * (2 * yl) ≤ stW M st + 8 * stCap M st) ∨
      (InRanges (stW S.mem st + 8 * stLen M st) (8 * (2 * yl)) R.rt ∧
        ApartAll (stW S.mem st + 8 * stLen M st) (8 * (2 * yl)) L1) := by
    rcases hscrL.loc with ⟨h0, h1, h2⟩ | ⟨hin, hap⟩
    · rw [hlenP] at h1
      rcases harrP with ⟨e1, e2⟩ | ⟨hin, hap⟩
      · rw [e1] at h1 h2; rw [e2] at h2; exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩
    · exact Or.inr ⟨hin, fun r hr => hap r (hq0.ext.mem_old hr)⟩
  have hPgA : 0 < stCap P.mem st → Apart (stW P.mem st + 8 * stLen P.mem st)
      (8 * (stCap P.mem st - stLen P.mem st)) RunIface.gA 32 := by
    intro _
    rcases harrP with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e1, e2, hlenP, eW, eL, eC]; exact hfgA
    · have := NatSub.outside_of_inRanges hgrt hin; unfold Apart; omega
  have hsepT : StkSep S.mem st (stW S.mem st + 8 * stLen M st) (8 * (2 * yl)) := by
    refine ⟨(hscrL.apart (hq0.ext.held (hq0.core.ext.held hsth)) fun _ => ?_).symm, ?_, hscrL.apart (Or.inr hgrt) fun hc => (hPgA hc).symm⟩
    · have := hstkP.2; unfold Apart at this ⊢; omega
    · simp only [BasicSqr.freeP, BasicSqr.freeN]; rw [hlen]; unfold Apart
      simp only [StackNat.rnd]; omega
  -- `p[0:m+n]` kept
  have hpH1 : Held R L1 p (8 * (xl + yl)) := by
    rcases hq0.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := hq0.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact hq0.core.ext.held ((hzl (by omega)).2.1.sub (Nat.le_refl _) (by omega))
    · exact Or.inl (hin1.sub (Nat.le_refl _) (by omega))
  have hpst := hq0.core.pst (by omega)
  have hpf := hq0.core.pfree (by omega)
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hpf
  have hpfree : Apart p (8 * (xl + yl)) (stW P.mem st + 8 * stLen P.mem st) (8 * (stCap P.mem st - stLen P.mem st)) := by
    rcases harrP with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2, hlenP, eW, eL, eC]; unfold Apart at hpf ⊢; omega
    · have := apart_of_held hpH1 hin hap; unfold Apart at this ⊢; omega
  have hpv : natVal S.mem p (xl + yl) = natVal P.mem p (xl + yl) := by
    unfold natVal
    refine Held.readLE2 (hq0.ext.held hpH1) hF' hLF ?_ ?_
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [stkWs, outside_cons, outside_nil, and_true]; unfold Apart at hpst hpfree; omega
  refine ⟨Lk', bk', ?_, ⟨hkT, by omega, fun _ => ⟨hscrL.al, hscrL.held, hscrL.acc, hscrL.b48⟩, hloc, hsepT⟩,
    hr0 hkT, hr1, hr2, by rw [hpv]; exact h.val⟩
  exact
    { core := hq0.core, h40 := h40, hlt := hq0.hlt, ext := hq0.ext.trans hext,
      bud := by have := hq0.bud; unfold lsp; omega,
      inv := by rw [h.g] at hinv; exact hinv, reg := hreg.trans hq0.reg, fr := hfr, lf := hlf, sok := hok,
      slen := hlen,
      sarr := by
        by_cases hc : stLen M st + StackNat.rnd (2 * yl) ≤ stCap P.mem st
        · obtain ⟨e1, e2⟩ := hsame (by rw [hlenP]; exact hc)
          rw [e1, e2]; exact harrP
        · obtain ⟨hin, hap⟩ := hgrow (by rw [hlenP]; omega)
          exact Or.inr ⟨hin, fun r hr => hap r (hq0.ext.mem_old hr)⟩,
      smem := by
        refine ArrIn.trans hmemP (fun hn => ?_) hext
        by_cases hc : stLen M st + StackNat.rnd (2 * yl) ≤ stCap P.mem st
        · exact absurd (hsame (by rw [hlenP]; exact hc)) hn
        · rw [hlenP] at hmem
          have hlcS := hok.2.2.2.2.2.1
          simp only [StackNat.rnd] at hlen hc
          exact ⟨hmem (by omega), by simp only [stLen, stCap] at hlen hlcS ⊢; omega⟩,
      lr := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.lr,
      fp := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.fp,
      b94 := (hrd _ _ (by omega) (by omega) (by omega)).trans h.b94,
      b95 := (hrd _ _ (by omega) (by omega) (by omega)).trans h.b95,
      c96 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.c96,
      n120 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.n120,
      p144 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.p144,
      s184 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.s184,
      dfn := (hrd _ _ (by omega) (by omega) (by omega)).trans h.dfn,
      dst := (hrd _ _ (by omega) (by omega) (by omega)).trans h.dst,
      dln := (hrd _ _ (by omega) (by omega) (by omega)).trans h.dln,
      dpt := (hrd _ _ (by omega) (by omega) (by omega)).trans h.dpt,
      a296 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.a296,
      a304 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.a304,
      a312 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.a312,
      a320 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.a320,
      a328 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.a328,
      a336 := (hrd _ _ (by omega) (by omega) (by omega)).trans hq0.a336 }

end

end FvModexp.Arm64.NatMul
