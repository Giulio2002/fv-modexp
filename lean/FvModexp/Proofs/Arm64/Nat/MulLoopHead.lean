import FvModexp.Proofs.Arm64.Nat.MulLoopStep

/-!
# `nat.mul` (arm64), chunk loop: the loop-head relation `LH` and the after-call relation `LM`

Loop (natmul.go:56-59), `SP' = SP - 256`, head `0x1bb204` (`R3 = i`, `R0..R2 = t`), the chunk product's call
`0x1bb260`, its return `0x1bb264`, `addTo(z[i:], t)` at `0x1bb1f0`, back to the head with `i + n` from `136(SP')`.
`k` = the number of chunks done (`i = (k + 1)·n`, `k·n < m`):
* `LH … Lk bk k tp tl tc S` at the head: `LB` (spent `lsp ℓ n k`), registers, `t = (tp, tl, tc)` (`TOK`), the value
  `z[0:m+n] = X[0:min(i, m)]·Y`;
* `LM … Lk bk k tp tl tc S` at `0x1bb264` (`i < m`): `LB` (spent `lsp ℓ n (k + 1)`), the result `t = X[i:i+cc]·Y` with
  `cc = min(n, m - i)`, the slots `128 = i`, `136 = i + n`, `z[0:m+n] = X[0:i]·Y`.
Budget lemmas `lsp_call` (the chunk product's budget at the head), `lsp_step`, `lsp_end` (`makeB + lsp ≤ mulC`).
`LB.wk` (weaken `spent`), `LB.winKeep` (own stores in the window keep `LB`, `TOK`, the values).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

/-- the budget spent at the loop head after `k` chunks (`ℓ` = the stack length at the entry) -/
@[reducible] def lsp (ℓ n k : Nat) : Nat := KC ℓ n + stackNatCost ℓ (2 * n) + k * MC (ℓ + rnd (2 * n)) n n

theorem mulC_gt {ℓ m n : Nat} (h : n < m) : mulC ℓ m n = MC ℓ m n := by
  unfold mulC; rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]

/-- the chunk product's budget: what is left at the head covers one more `MC ℓ1 n n` -/
theorem lsp_call {ℓ m n k b b1 bk : Nat} (h40 : 40 ≤ n) (hk : (k + 1) * n < m) (hb : mulC ℓ m n ≤ b)
    (h1 : b - makeB (m + n) ≤ b1) (h2 : b1 - lsp ℓ n k ≤ bk) : MC (ℓ + rnd (2 * n)) n n ≤ bk := by
  have hn : n ≤ (k + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hL := MC_loop (ℓ := ℓ) h40 (by omega : n < m)
  rw [mulC_gt (by omega : n < m)] at hb
  have hq : k + 1 ≤ (m - 1) / n := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hm := Nat.mul_le_mul_right (MC (ℓ + rnd (2 * n)) n n) hq
  have : (k + 1) * MC (ℓ + rnd (2 * n)) n n = k * MC (ℓ + rnd (2 * n)) n n + MC (ℓ + rnd (2 * n)) n n := by rw [Nat.add_mul, Nat.one_mul]
  unfold lsp at h2
  omega

theorem lsp_step (ℓ n k : Nat) : lsp ℓ n k + MC (ℓ + rnd (2 * n)) n n = lsp ℓ n (k + 1) := by
  have : (k + 1) * MC (ℓ + rnd (2 * n)) n n = k * MC (ℓ + rnd (2 * n)) n n + MC (ℓ + rnd (2 * n)) n n := by rw [Nat.add_mul, Nat.one_mul]
  unfold lsp; omega

/-- at the exit: the whole loop fits `mulC` -/
theorem lsp_end {ℓ m n k : Nat} (h40 : 40 ≤ n) (hnm : n < m) (hk : k * n < m) :
    makeB (m + n) + lsp ℓ n k ≤ mulC ℓ m n := by
  have hL := MC_loop (ℓ := ℓ) h40 hnm
  rw [mulC_gt hnm]
  have hq : k ≤ (m - 1) / n := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hm := Nat.mul_le_mul_right (MC (ℓ + rnd (2 * n)) n n) hq
  unfold lsp
  omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

/-- weaken the spent budget -/
theorem LB.wk (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {spent' : Nat}
    (hs : spent ≤ spent') : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent' Mi :=
  { h with bud := by have := h.bud; omega }

/-- the stack header is outside the window -/
theorem LB.hdrWin (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    (hF : MemFrame Mi Mi' (winA s W 88)) :
    stW Mi' st = stW Mi st ∧ stLen Mi' st = stLen Mi st ∧ stCap Mi' st = stCap Mi st := by
  obtain ⟨hW, hWs, -⟩ := h.lay
  have hko := h.lwsOut
  have hst : Outside st 24 (winA s W 88) := by
    have := hko _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [winA, outside_cons, outside_nil, and_true]; simp only at this; omega
  exact ⟨hF.readLE _ _ (hst.of_sub (Nat.le_refl _) (by omega)), hF.readLE _ _ (hst.of_sub (by omega) (by omega)),
    hF.readLE _ _ (hst.of_sub (by omega) (by omega))⟩

/-- `TOK` survives writes inside the window -/
theorem TOK.winKeep (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {tp tc : Nat}
    (ht : TOK R L1 Lk M Mi st tp tc) {Mi' : Memory} (hF : MemFrame Mi Mi' (winA s W 88)) :
    TOK R L1 Lk M Mi' st tp tc := by
  obtain ⟨eW, eL, eC⟩ := h.hdrWin hF
  obtain ⟨h0, h40, hl, hloc, h1, h2, h3⟩ := ht
  refine ⟨h0, h40, fun hc => ?_, hloc, h1, ?_, h3⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · simp only [BasicSqr.freeP, BasicSqr.freeN] at h2 ⊢; rw [eW, eL, eC]; exact h2

/-- `p[0:m+n]` and `t` keep their values under writes inside the window -/
theorem LB.winVal (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {tp tc tl : Nat}
    (ht : TOK R L1 Lk M Mi st tp tc) (htl : tl ≤ tc) {Mi' : Memory} (hF : MemFrame Mi Mi' (winA s W 88)) :
    natVal Mi' p (xl + yl) = natVal Mi p (xl + yl) ∧ natVal Mi' tp tl = natVal Mi tp tl := by
  have hpw := h.core.pw
  have hcap := h.core.cap
  obtain ⟨htw, -⟩ := h.tsep ht
  exact ⟨natVal_frame hF (winA_of_win' (hpw.of_sub (Nat.le_refl _) (by omega))),
    natVal_frame hF (winA_of_win' (htw.of_sub (Nat.le_refl _) (by omega)))⟩

end

/-- **the loop head** `0x1bb204` after `k` chunks (`i = (k + 1)·n`; see the module doc) -/
structure LH (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk k tp tl tc : Nat)
    (S : State) : Prop where
  lb : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp (stLen M st) yl k) S.mem
  pc : S.pc = BitVec.ofNat 64 0x1bb204
  sp : S.sp = s.sp - 256#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 264#64
  x18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 tp
  r1 : S.regs 1 = BitVec.ofNat 64 tl
  r2 : S.regs 2 = BitVec.ofNat 64 tc
  r3 : S.regs 3 = BitVec.ofNat 64 ((k + 1) * yl)
  klt : k * yl < xl
  tok : TOK R L1 Lk M S.mem st tp tc
  px : Apart p (8 * c) xp (8 * xl)
  py : Apart p (8 * c) yp (8 * yl)
  val : natVal S.mem p (xl + yl) = natVal s.mem xp (min ((k + 1) * yl) xl) * natVal s.mem yp yl

/-- **after the chunk product** (`0x1bb264`, `i = (k + 1)·n < m`; `t = (tp, tl, tc)` the product) -/
structure LM (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk k tp tl tc : Nat)
    (S : State) : Prop where
  lb : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (lsp (stLen M st) yl (k + 1)) S.mem
  pc : S.pc = BitVec.ofNat 64 0x1bb264
  sp : S.sp = s.sp - 256#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 264#64
  x18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 tp
  r1 : S.regs 1 = BitVec.ofNat 64 tl
  r2 : S.regs 2 = BitVec.ofNat 64 tc
  ilt : (k + 1) * yl < xl
  m128 : S.mem.readLE (s.sp.toNat - 128) 8 = (k + 1) * yl
  m136 : S.mem.readLE (s.sp.toNat - 120) 8 = (k + 1) * yl + yl
  tok : TOK R L1 Lk M S.mem st tp tc
  px : Apart p (8 * c) xp (8 * xl)
  py : Apart p (8 * c) yp (8 * yl)
  tlc : tl ≤ tc
  tll : (k + 1) * yl + tl ≤ xl + yl
  tv : natVal S.mem tp tl =
    natVal s.mem (xp + 8 * ((k + 1) * yl)) (min yl (xl - (k + 1) * yl)) * natVal s.mem yp yl
  val : natVal S.mem p (xl + yl) = natVal s.mem xp ((k + 1) * yl) * natVal s.mem yp yl

end FvModexp.Arm64.NatMul
