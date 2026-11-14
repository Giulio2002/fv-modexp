import FvModexp.Proofs.Amd64.Exp.NStkNilE

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: from `Get`'s return (pooled stack) / `newobject`'s return to the `nat.rem` entry
| `J4` (agent expmc s74; twin of `Arm64.ExpN.getT` / `noRet`, directly on `LibNE`)

nat.go:287-289, 677-681 (`RSP = t - 0x108`). `getTE`: `Get` returned `(type:*big.stack, d)`, `d ≠ 0` (`CMPQ AX, CX`
equal, `TESTQ BX` non-zero), `DX := [t + 0x10]` (`len y`), `CMPQ DX, 1`, `JMP` join. `noRetE`: `newobject` returned
`d` (`CX := [t + 0x10]`, `CMPQ CX, 1`, `BX := d`). The join fn+0x351: the defer record (`[t - 0x30] := deferwrap1`,
`[t - 0x28] := d`, `[t - 0x10] := t - 0x30`, byte `t - 0x99 := 1`), the reloads (`AX, CX = [t - 0x38], [t - 0x70]`
(`z`), `DX = [t + 0x18]` (`cap y`), `SI, R8, R9, R10 = x, slow` spills, `R11, R12, R13, R15 = [t + 0x28], [t + 8],
[t + 0x20], [t + 0x10]`), byte `t - 0x9a := 1`, `DI := d`, `BX := [t - 0x80]`; then as in `NStk.stk`:
`len y == 1 && y[0] == 1` → `rem`'s entry, else `J4`. Continuation form (`NilJK`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `nat.expNN.deferwrap1` (`0x5e79e0`) -/
abbrev dwA : Nat := 6191584

theorem dwA_eq : segAddr Extracted.program Free.fn = dwA := by decide

/-- the two continuations after the join (`rem`'s entry | `J4`), from memory `M` at the join's predecessor `S0`, the
spilled values `z0 zl zc` (`z`), `yc`, `x6 x8 x9 b10` (`x`, slow), `n yp mp yl mc` and the stack `d` -/
def NilJK (impl : List Amd64.Segment) (ret0 : Nat) (Q : Amd64.Outcome → Prop) (t d : Nat) (S0 : State)
    (M : Janus.Arm64.Memory) (z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc : Nat) : Prop :=
  (yl = 1 → M.readLE yp 8 = 1 → ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 remA → S'.regs 4 = BitVec.ofNat 64 (t - 0x110) →
      S'.regs 0 = BitVec.ofNat 64 z0 → S'.regs 3 = BitVec.ofNat 64 zl → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 7 = BitVec.ofNat 64 d → S'.regs 6 = BitVec.ofNat 64 x6 → S'.regs 8 = BitVec.ofNat 64 x8 →
      S'.regs 9 = BitVec.ofNat 64 x9 → S'.regs 5 = S0.regs 5 →
      S'.regs 14 = S0.regs 14 → S'.fsBase = S0.fsBase → S'.df = S0.df → S'.xmm 15 = S0.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x110, t - 0xf0), (t - 0x9a, t - 0x98), (t - 0x30, t - 0x20), (t - 0x10, t - 8)] →
      M'.regions = M.regions →
      M'.readLE (t - 0x110) 8 = remR → M'.readLE (t - 0x108) 8 = mp → M'.readLE (t - 0x100) 8 = n →
      M'.readLE (t - 0xf8) 8 = mc → M'.readLE (t - 0x9a) 1 = 1 → M'.readLE (t - 0x99) 1 = 1 →
      M'.readLE (t - 0x30) 8 = dwA → M'.readLE (t - 0x28) 8 = d → M'.readLE (t - 0x10) 8 = t - 0x30 →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q) ∧
  (¬(yl = 1 ∧ M.readLE yp 8 = 1) → ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 6190084 → S'.regs 4 = S0.regs 4 →
      S'.regs 0 = BitVec.ofNat 64 z0 → S'.regs 3 = BitVec.ofNat 64 zl → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 7 = BitVec.ofNat 64 d → S'.regs 6 = BitVec.ofNat 64 x6 → S'.regs 8 = BitVec.ofNat 64 x8 →
      S'.regs 9 = BitVec.ofNat 64 x9 → S'.regs 10 = BitVec.ofNat 64 b10 → S'.regs 11 = BitVec.ofNat 64 n →
      S'.regs 12 = BitVec.ofNat 64 yp → S'.regs 13 = BitVec.ofNat 64 mp → S'.regs 15 = BitVec.ofNat 64 yl →
      S'.regs 2 = BitVec.ofNat 64 yc → S'.regs 5 = S0.regs 5 →
      S'.regs 14 = S0.regs 14 → S'.fsBase = S0.fsBase → S'.df = S0.df → S'.xmm 15 = S0.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x9a, t - 0x98), (t - 0x30, t - 0x20), (t - 0x10, t - 8)] → M'.regions = M.regions →
      M'.readLE (t - 0x9a) 1 = 1 → M'.readLE (t - 0x99) 1 = 1 →
      M'.readLE (t - 0x30) 8 = dwA → M'.readLE (t - 0x28) 8 = d → M'.readLE (t - 0x10) 8 = t - 0x30 →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q)

/-- the spills the join reloads -/
def NilSp (M : Janus.Arm64.Memory) (t z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc : Nat) : Prop :=
  M.readLE (t - 0x38) 8 = z0 ∧ M.readLE (t - 0x80) 8 = zl ∧ M.readLE (t - 0x70) 8 = zc ∧
  M.readLE (t + 0x18) 8 = yc ∧ M.readLE (t + 0x58) 8 = x6 ∧ M.readLE (t + 0x60) 8 = x8 ∧
  M.readLE (t + 0x68) 8 = x9 ∧ M.readLE (t + 0x70) 1 = b10 ∧ M.readLE (t + 0x28) 8 = n ∧
  M.readLE (t + 8) 8 = yp ∧ M.readLE (t + 0x20) 8 = mp ∧ M.readLE (t + 0x10) 8 = yl ∧ M.readLE (t + 0x30) 8 = mc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.unusedSimpArgs false in
/-- `Get` returned a pooled stack `d ≠ 0` -/
theorem getTE (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t d z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hd : d < 2 ^ 64) (hd0 : 0 < d) (hsp : NilSp M t z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc)
    (hy0 : yl ≠ 0) (hya : M.accessible yp 8 false = true) (hyo : yp + 8 ≤ t - 0x110 ∨ t + 0x78 ≤ yp)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 getR) (hS4 : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h0 : S.regs 0 = BitVec.ofNat 64 Free.stkT) (h3 : S.regs 3 = BitVec.ofNat 64 d) (hmem : S.mem = M)
    (hK : NilJK impl ret0 Q t d S M z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc) :
    Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hsp
  obtain ⟨KR, KD⟩ := hK
  have hy8 : M.readLE yp 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := r11 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := r9 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := r10 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hn : n < 2 ^ 64 := r8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hb10 : b10 < 2 ^ 8 := r7 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := r12 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have a38 : t - 0x108 + 0xd0 = t - 0x38 := by omega
  have a80 : t - 0x108 + 0x88 = t - 0x80 := by omega
  have a70 : t - 0x108 + 0x98 = t - 0x70 := by omega
  have a18 : t - 0x108 + 0x120 = t + 0x18 := by omega
  have a58 : t - 0x108 + 0x160 = t + 0x58 := by omega
  have a60 : t - 0x108 + 0x168 = t + 0x60 := by omega
  have a68 : t - 0x108 + 0x170 = t + 0x68 := by omega
  have a78 : t - 0x108 + 0x178 = t + 0x70 := by omega
  have a28 : t - 0x108 + 0x130 = t + 0x28 := by omega
  have a08 : t - 0x108 + 0x110 = t + 8 := by omega
  have a20 : t - 0x108 + 0x128 = t + 0x20 := by omega
  have a10 : t - 0x108 + 0x118 = t + 0x10 := by omega
  have a30 : t - 0x108 + 0x138 = t + 0x30 := by omega
  have a6e : t - 0x108 + 0x6e = t - 0x9a := by omega
  have a6f : t - 0x108 + 0x6f = t - 0x99 := by omega
  have ad8 : t - 0x108 + 0xd8 = t - 0x30 := by omega
  have ae0 : t - 0x108 + 0xe0 = t - 0x28 := by omega
  have af8 : t - 0x108 + 0xf8 = t - 0x10 := by omega
  have bd : (BitVec.ofNat 64 d = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  have h0' : S.regs 0 = 0x7170a0#64 := by rw [h0]; rfl
  clear h0
  subst hmem
  janus64_run [es1, a38, a80, a70, a18, a58, a60, a68, a78, a28, a08, a20, a10, a30, h0', bd, a6e, a6f, ad8, ae0, af8, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
    r11, r12] until [remA, 6190084]
  · have e1 : yl = 1 := by omega
    have e2 : S.mem.readLE yp 8 = 1 := by omega
    refine KR e1 e2 _ _ ?ar0 ?ar1 ?ar2 ?ar3 ?ar4 ?ar5 ?ar6 ?ar7 ?ar8 ?ar9 ?ar10 ?ar11 ?ar12 ?ar13
      rfl ?amf ?arg ?aq0 ?aq1 ?aq2 ?aq3 ?aq4 ?aq5 ?aq6 ?aq7 ?aq8
    case amf => janus_frame
    case arg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case ar0 | ar1 | ar10 | ar11 | ar12 | ar13 => rfl
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12] <;> omega)
  · have e2 : ¬S.mem.readLE yp 8 = 1 := by omega
    refine KD (fun h => e2 h.2) _ _ ?br0 ?br1 ?br2 ?br3 ?br4 ?br5 ?br6 ?br7 ?br8 ?br9
      ?br10 ?br11 ?br12 ?br13 ?br14 ?br15 ?br16 ?br17 ?br18 ?br19
      rfl ?bmf ?brg ?bq0 ?bq1 ?bq2 ?bq3 ?bq4
    case bmf => janus_frame
    case brg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case br0 | br1 | br15 | br16 | br17 | br18 | br19 => rfl
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12] <;> omega)
  · have e1 : ¬yl = 1 := by omega
    refine KD (fun h => e1 h.1) _ _ ?cr0 ?cr1 ?cr2 ?cr3 ?cr4 ?cr5 ?cr6 ?cr7 ?cr8 ?cr9
      ?cr10 ?cr11 ?cr12 ?cr13 ?cr14 ?cr15 ?cr16 ?cr17 ?cr18 ?cr19
      rfl ?cmf ?crg ?cq0 ?cq1 ?cq2 ?cq3 ?cq4
    case cmf => janus_frame
    case crg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case cr0 | cr1 | cr15 | cr16 | cr17 | cr18 | cr19 => rfl
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12] <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.unusedSimpArgs false in
/-- `newobject(type:big.stack)` returned `d` -/
theorem noRetE (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t d z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hd : d < 2 ^ 64) (hd0 : 0 < d) (hsp : NilSp M t z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc)
    (hy0 : yl ≠ 0) (hya : M.accessible yp 8 false = true) (hyo : yp + 8 ≤ t - 0x110 ∨ t + 0x78 ≤ yp)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 noR) (hS4 : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h0 : S.regs 0 = BitVec.ofNat 64 d) (hmem : S.mem = M)
    (hK : NilJK impl ret0 Q t d S M z0 zl zc yc x6 x8 x9 b10 n yp mp yl mc) :
    Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hsp
  obtain ⟨KR, KD⟩ := hK
  have hy8 : M.readLE yp 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := r11 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := r9 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := r10 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hn : n < 2 ^ 64 := r8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hb10 : b10 < 2 ^ 8 := r7 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := r12 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have a38 : t - 0x108 + 0xd0 = t - 0x38 := by omega
  have a80 : t - 0x108 + 0x88 = t - 0x80 := by omega
  have a70 : t - 0x108 + 0x98 = t - 0x70 := by omega
  have a18 : t - 0x108 + 0x120 = t + 0x18 := by omega
  have a58 : t - 0x108 + 0x160 = t + 0x58 := by omega
  have a60 : t - 0x108 + 0x168 = t + 0x60 := by omega
  have a68 : t - 0x108 + 0x170 = t + 0x68 := by omega
  have a78 : t - 0x108 + 0x178 = t + 0x70 := by omega
  have a28 : t - 0x108 + 0x130 = t + 0x28 := by omega
  have a08 : t - 0x108 + 0x110 = t + 8 := by omega
  have a20 : t - 0x108 + 0x128 = t + 0x20 := by omega
  have a10 : t - 0x108 + 0x118 = t + 0x10 := by omega
  have a30 : t - 0x108 + 0x138 = t + 0x30 := by omega
  have a6e : t - 0x108 + 0x6e = t - 0x9a := by omega
  have a6f : t - 0x108 + 0x6f = t - 0x99 := by omega
  have ad8 : t - 0x108 + 0xd8 = t - 0x30 := by omega
  have ae0 : t - 0x108 + 0xe0 = t - 0x28 := by omega
  have af8 : t - 0x108 + 0xf8 = t - 0x10 := by omega
  have bd : (BitVec.ofNat 64 d = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  subst hmem
  janus64_run [es1, a38, a80, a70, a18, a58, a60, a68, a78, a28, a08, a20, a10, a30, h0, bd, a6e, a6f, ad8, ae0, af8, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
    r11, r12] until [remA, 6190084]
  · have e1 : yl = 1 := by omega
    have e2 : S.mem.readLE yp 8 = 1 := by omega
    refine KR e1 e2 _ _ ?ar0 ?ar1 ?ar2 ?ar3 ?ar4 ?ar5 ?ar6 ?ar7 ?ar8 ?ar9 ?ar10 ?ar11 ?ar12 ?ar13
      rfl ?amf ?arg ?aq0 ?aq1 ?aq2 ?aq3 ?aq4 ?aq5 ?aq6 ?aq7 ?aq8
    case amf => janus_frame
    case arg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case ar0 | ar1 | ar10 | ar11 | ar12 | ar13 => rfl
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12] <;> omega)
  · have e2 : ¬S.mem.readLE yp 8 = 1 := by omega
    refine KD (fun h => e2 h.2) _ _ ?br0 ?br1 ?br2 ?br3 ?br4 ?br5 ?br6 ?br7 ?br8 ?br9
      ?br10 ?br11 ?br12 ?br13 ?br14 ?br15 ?br16 ?br17 ?br18 ?br19
      rfl ?bmf ?brg ?bq0 ?bq1 ?bq2 ?bq3 ?bq4
    case bmf => janus_frame
    case brg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case br0 | br1 | br15 | br16 | br17 | br18 | br19 => rfl
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12] <;> omega)
  · have e1 : ¬yl = 1 := by omega
    refine KD (fun h => e1 h.1) _ _ ?cr0 ?cr1 ?cr2 ?cr3 ?cr4 ?cr5 ?cr6 ?cr7 ?cr8 ?cr9
      ?cr10 ?cr11 ?cr12 ?cr13 ?cr14 ?cr15 ?cr16 ?cr17 ?cr18 ?cr19
      rfl ?cmf ?crg ?cq0 ?cq1 ?cq2 ?cq3 ?cq4
    case cmf => janus_frame
    case crg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case cr0 | cr1 | cr15 | cr16 | cr17 | cr18 | cr19 => rfl
    all_goals first
      | (janus64_simp; done)
      | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12] <;> omega)

end FvModexp.Amd64.ExpN
