import FvModexp.Proofs.Arm64.Exp.W4Pow

/-!
# window-4 prologue (arm64): the whole table loop `for i := 2; i < 16; i++` (nat.go:1415-1417)

Induction on `16 - i` over `W4Pow.powStep`; the exit `i = 16` jumps to `j4` with all 16 entries.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem powLoop (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 bp bc : Nat) (M0 : Memory) (r18 r29 : BitVec 64)
    (tbl : Nat → Nat) (hs : PStatic R L g sp n mp mc k0 bp bc M0)
    (htbl : ∀ i, 2 ≤ i → i < 16 → tbl i = Exp.montgomery n (tbl (i - 1)) (tbl 1) (M0.readLE mp (8 * n)) k0)
    (KX : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 j4 → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      FP R L sp bp bc M0 M' → R.inv b L g (view R.rt L M') → M'.regions = M0.regions →
      (∀ d, d < 16 → Ent sp n bp tbl M' d) → Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    ∀ (f i : Nat) (S : State) (M : Memory), f = 16 - i → 2 ≤ i → i ≤ 16 →
      S.pc = BitVec.ofNat 64 powHead → S.sp = BitVec.ofNat 64 sp → S.regs 0 = BitVec.ofNat 64 i →
      S.regs 18 = r18 → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 → S.mem = M →
      FP R L sp bp bc M0 M → R.inv b L g (view R.rt L M) → M.regions = M0.regions →
      (∀ d, d < i → Ent sp n bp tbl M d) → Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  intro f
  induction f with
  | zero =>
    intro i S M hf hi2 hi16 hpc hsp h0 h18 h28 h29 hmem hF hinv hrg hE
    have hi : i = 16 := by omega
    subst hi
    janus_run [] until [j4]
    refine KX _ _ ?_ ?_ ?_ ?_ ?_ ?_ hF hinv hrg hE
    all_goals first | (janus_simp; done) | skip
  | succ f ih =>
    intro i S M hf hi2 hi16 hpc hsp h0 h18 h28 h29 hmem hF hinv hrg hE
    refine powStep impl hap R hclr hmv ret hret Q b L g sp n mp mc k0 bp bc M0 r18 r29 tbl hs i S M hi2 (by omega)
      hpc hsp h0 h18 h28 h29 hmem hF hinv hrg hE ?_
    intro S' M' a1 a2 a3 a4 a5 a6 a7 hF' hinv' hrg' hE' hEi
    refine ih (i + 1) S' M' (by omega) (by omega) (by omega) a1 a2 a3 a4 a5 a6 a7 hF' hinv' hrg' ?_
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
    · exact hE' d hd
    · exact ⟨hEi.1.trans (htbl d hi2 (by omega)).symm, hEi.2⟩

end FvModexp.Arm64.W4Pro
