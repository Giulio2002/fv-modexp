import FvModexp.Proofs.Amd64.Nat.DivBasicRec

set_option autoImplicit false
set_option maxRecDepth 20000

/-!
# `divBasic` (amd64): the memory facts at the loop head (pure; agent top s23)

`head_mem`: `Mem` of the head memory `recMem S2 …` (the memory after the inlined `reciprocalWord`) from the facts at
the `stk.nat` call (`AtNat`), after its return (`AfterNat`) and `Env`. `head_qu`: `q` and `u` unchanged since the entry.
Split out of `pro3` (DivBasicPro3) so that no run state is in the context of the omega calls here.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

/-- reads of `P.mem` outside the prologue's writes -/
theorem rdP {s P : State} (hF : MemFrame s.mem P.mem (proWs s)) (a n : Nat)
    (h : a + n ≤ (s.regs 4).toNat - 137 ∨ (s.regs 4).toNat + 88 ≤ a ∨
      ((s.regs 4).toNat ≤ a ∧ a + n ≤ (s.regs 4).toNat + 32)) : P.mem.readLE a n = s.mem.readLE a n :=
  hF.readLE _ _ (by simp only [proWs, outside_cons, outside_nil, and_true]; omega)

/-- reads of `S2.mem` in the frame above the callee's window `[sp-4424, sp-208)` -/
theorem rdS2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hpre : Pre R b L qp ql st up ul uc vp vl s)
    (hA : AfterNat R b L st vl s P S2 L1 b1) (a n : Nat) (h1 : (s.regs 4).toNat - 208 ≤ a)
    (h2 : a + n ≤ (s.regs 4).toNat + 88) : S2.mem.readLE a n = P.mem.readLE a n := by
  have hout := hpre.ce.2.2.2.2.1
  have hb := hpre.ce.2.1
  simp only [StackWritable, regSP] at hb
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hfw := hpre.stfw; simp only [win, outside_cons, outside_nil, and_true, freeP, freeN] at hfw
  have hlc := hpre.stok.2.2.2.2.2.1
  obtain ⟨hb1, hb2, -⟩ := hb
  rw [hA.F2.readLE _ _ ?_, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega, by omega⟩

/-- one held object (apart from the window, the stack header and the free part) in `S2.mem` -/
theorem rdS2r {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hF : MemFrame s.mem P.mem (proWs s)) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (x n0 : Nat) (hH : Held R L x n0) (hsp0 : 4424 ≤ (s.regs 4).toNat)
    (hw : x + n0 ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ x) (hs : Apart st 24 x n0)
    (hf : Apart x n0 (freeP s.mem st) (freeN s.mem st)) (a n : Nat) (h1 : x ≤ a) (h2 : a + n ≤ x + n0) :
    S2.mem.readLE a n = s.mem.readLE a n := by
  simp only [freeP, freeN] at hf
  unfold Apart at hs hf
  rw [Held.readLE2 (hH.sub h1 h2) hA.F2 hA.LF2
    (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), rdP hF a n (by omega)]

/-- `v`, `q` and `u` in `S2.mem` (the prologue and `stk.nat` do not write them) -/
theorem rdS2v {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {t w1 c1 : Nat} (hpre : Pre R b L qp ql st up ul uc vp vl s)
    (hP : AtNat R b L qp ql st up ul uc vp vl s P) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) (a n : Nat)
    (h : (vp ≤ a ∧ a + n ≤ vp + 8 * vl) ∨ (qp ≤ a ∧ a + n ≤ qp + 8 * ql) ∨ (up ≤ a ∧ a + n ≤ up + 8 * ul)) :
    S2.mem.readLE a n = s.mem.readLE a n := by
  have hl := hE.lay
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact rdS2r hP.fr hA _ _ hpre.vh hl.sp0 hl.vw hpre.stv hpre.free.2.2 a n h1 h2
  · exact rdS2r hP.fr hA _ _ hpre.qh hl.sp0 hl.qw hpre.stq hpre.free.1 a n h1 h2
  · exact rdS2r hP.fr hA _ _ hpre.uh hl.sp0 hl.uw hpre.stu hpre.free.2.1 a n h1 h2

/-- the memory written by the inlined `reciprocalWord` block: reads elsewhere -/
theorem rdRec (M : Memory) (sp V vl t rc a n : Nat) (hsp : 136 ≤ sp) (h1 : a + n ≤ sp - 136 ∨ sp - 128 ≤ a)
    (h2 : a + n ≤ sp - 120 ∨ sp - 112 ≤ a) (h3 : a + n ≤ sp - 72 ∨ sp - 48 ≤ a) :
    (recMem M sp V vl t rc).readLE a n = M.readLE a n := by
  simp only [recMem]
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

/-- `q` and `u` at the head are those of the entry -/
theorem head_qu {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {t w1 c1 : Nat} (hpre : Pre R b L qp ql st up ul uc vp vl s)
    (hP : AtNat R b L qp ql st up ul uc vp vl s P) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) (V rc : Nat) :
    ∀ a n, (qp ≤ a ∧ a + n ≤ qp + 8 * ql) ∨ (up ≤ a ∧ a + n ≤ up + 8 * ul) →
      (recMem S2.mem (s.regs 4).toNat V vl t rc).readLE a n = s.mem.readLE a n := by
  intro a n h
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hqw := hl.qw; have huw := hl.uw
  rw [rdRec _ _ _ _ _ _ a n (by omega) (by omega) (by omega) (by omega)]
  exact rdS2v hpre hP hA hE a n (by omega)

/-- the TLS slot at the head -/
theorem head_tls {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {t w1 c1 : Nat} (hpre : Pre R b L qp ql st up ul uc vp vl s)
    (hP : AtNat R b L qp ql st up ul uc vp vl s P) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) {V rc : Nat} :
    (recMem S2.mem (s.regs 4).toNat V vl t rc).readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have htl := hl.tlw; have hts := hl.tls
  have htT := hpre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨-, -, htg⟩, htr, -⟩ := htT
  have hft := hpre.stft; simp only [freeP, freeN] at hft; unfold Apart at hft
  rw [rdRec _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), hA.F2.readLE _ _ ?_,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), rdP hP.fr _ _ (by omega)]
  · exact htg
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
  exact ⟨⟨htr, by omega⟩, by omega, by omega⟩

/-- the memory frame from the entry to the head -/
theorem head_fr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {t w1 c1 : Nat}
    (hP : AtNat R b L qp ql st up ul uc vp vl s P) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) {V rc : Nat} :
    MemFrame s.mem (recMem S2.mem (s.regs 4).toNat V vl t rc)
      (R.rt ++ win s 4424 88 ++ wsL qp ql up ul vl t ++ stkWs s.mem st) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hW : MemFrame P.mem (P.mem.writeLE ((s.regs 4).toNat - 232) 8 raNat)
      [((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
     fun a n v => by simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
  have hS2 : MemFrame S2.mem (recMem S2.mem (s.regs 4).toNat V vl t rc)
      [((s.regs 4).toNat - 136, (s.regs 4).toNat - 48)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h; exact rdRec _ _ _ _ _ _ a n (by omega) (by omega) (by omega) (by omega),
     fun a n v => by simp only [recMem, Janus.Arm64.Memory.accessible_writeLE]⟩
  refine (mfTrans hP.fr (mfTrans hW (mfTrans hA.F2 hS2))).mono fun a n ho => ?_
  simp only [win, stkWs, wsL, proWs, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
  obtain ⟨hrt, hwin, -, -, -, h5, h6⟩ := ho
  exact ⟨by omega, by omega, by omega, hrt, by omega, h5, h6, by omega⟩

/-- the live frame from the entry to the head -/
theorem head_lf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {t w1 c1 : Nat}
    (hP : AtNat R b L qp ql st up ul uc vp vl s P) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) {V rc : Nat} :
    LiveFrame s.mem (recMem S2.mem (s.regs 4).toNat V vl t rc) L (wsL qp ql up ul vl t ++ stkWs s.mem st) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  refine ⟨fun a n hin hws => ?_⟩
  have hw0 : a + n ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ a := by
    obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; omega
  simp only [stkWs, wsL, outside_append, outside_cons, outside_nil, and_true] at hws
  obtain ⟨-, h7, h8⟩ := hws
  rw [rdRec _ _ _ _ _ _ a n (by omega) (by omega) (by omega) (by omega),
    hA.LF2.readLE a n hin (by simp only [stkWs, outside_cons, outside_nil, and_true]; exact ⟨h7, h8⟩),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), rdP hP.fr a n (by omega)]

set_option maxHeartbeats 4000000 in
/-- **`Mem` at the loop head** (memory `recMem S2 …` after the inlined `reciprocalWord`) -/
theorem head_mem {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s P S2 : State}
    {L1 : List (Nat × Nat)} {b1 : Nat} {t w1 c1 : Nat} (hpre : Pre R b L qp ql st up ul uc vp vl s)
    (hP : AtNat R b L qp ql st up ul uc vp vl s P) (hA : AfterNat R b L st vl s P S2 L1 b1)
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) (hw1 : stW S2.mem st = w1)
    (hc1 : stCap S2.mem st = c1) :
    Mem R L qp ql st up ul uc vp vl (s.mem.readLE ((s.regs 4).toNat + 24) 8) s t L1 b1 w1 c1
      (recMem S2.mem (s.regs 4).toNat (s.mem.readLE (vp + 8 * (vl - 1)) 8) vl t
        (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have ks : ∀ a n, ((s.regs 4).toNat - 208 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 136 ∨
      (s.regs 4).toNat - 104 ≤ a ∧ a + n ≤ (s.regs 4).toNat - 72 ∨
      (s.regs 4).toNat - 48 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 88) →
      (recMem S2.mem (s.regs 4).toNat (s.mem.readLE (vp + 8 * (vl - 1)) 8) vl t
        (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))).readLE a n = P.mem.readLE a n := by
    intro a n h
    rw [rdRec _ _ _ _ _ _ a n (by omega) (by omega) (by omega) (by omega), rdS2 hpre hA a n (by omega) (by omega)]
  have hV64 : s.mem.readLE (vp + 8 * (vl - 1)) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hvtop := hpre.vtop
  have hrl := FvModexp.AsmDivVW.recipWord_lt _ (by omega) hV64
  have ht48 := hl.t48
  refine ⟨?ra, (ks _ _ (by omega)).trans hP.bp, (ks _ _ (by omega)).trans hP.dbit, ?rw, ?hl,
    (ks _ _ (by omega)).trans hP.mm, ?vn, ?hc, ?tp, (ks _ _ (by omega)).trans hP.dfn, (ks _ _ (by omega)).trans hP.dst,
    (ks _ _ (by omega)).trans hP.dn, (ks _ _ (by omega)).trans hP.dp, ?s7, ?s8, ?s9, (ks _ _ (by omega)).trans hP.s1,
    (ks _ _ (by omega)).trans hP.s2, (ks _ _ (by omega)).trans hP.s4, (ks _ _ (by omega)).trans hP.s5,
    (ks _ _ (by omega)).trans hP.s6, ?hw, ?hlen, ?hcap, ?tls, ?vs, ?fr, ?lf, ?inv⟩
  case ra => rw [ks _ _ (by omega), rdP hP.fr _ _ (by omega)]
  case s7 => rw [ks _ _ (by omega), rdP hP.fr _ _ (by omega)]; exact hpre.vpS
  case s8 => rw [ks _ _ (by omega), rdP hP.fr _ _ (by omega)]; exact hpre.vlS
  case s9 => rw [ks _ _ (by omega), rdP hP.fr _ _ (by omega)]
  case rw => simp only [recMem, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hrl
  case hl =>
    simp only [recMem]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  case vn =>
    simp only [recMem]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hV64
  case hc =>
    simp only [recMem]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case tp =>
    simp only [recMem]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  case hw => have := hl.sw; rw [rdRec _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact hw1
  case hlen => have := hl.sw; rw [rdRec _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact hA.len
  case hcap => have := hl.sw; rw [rdRec _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact hc1
  case vs =>
    intro a n h1 h2
    have := hl.vw
    rw [rdRec _ _ _ _ _ _ a n (by omega) (by omega) (by omega) (by omega)]
    exact rdS2v hpre hP hA hE a n (Or.inl ⟨h1, h2⟩)
  case tls => exact head_tls hpre hP hA hE
  case fr => exact head_fr hP hA hE
  case lf => exact head_lf hP hA hE
  case inv =>
    have hout := hpre.ce.2.2.2.2.1
    simp only [recMem]
    refine inv_store_out (inv_store_out (inv_store_out (inv_store_out (inv_store_out hA.inv ?_) ?_) ?_) ?_) ?_ <;>
      exact hout.of_sub (by omega) (by omega)

end FvModexp.Amd64.DivBasic
