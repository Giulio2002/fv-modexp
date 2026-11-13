import FvModexp.Proofs.Amd64.Exp.MontW
import FvModexp.Proofs.Common.ExpOdd
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `expNNOddMontgomeryWindowSize2` (amd64), main loop nat.go:1579-1599: shared definitions (agent expmc s60)

Twin of `Amd64.W4Defs` / `Arm64.W2Defs`. Code map (function base `segAddr LibW.program fn` = 0x5ec400, frame
`PUSHQ BP; SUBQ $0x268`, `sp` = the `RSP` inside the frame): loop test `TESTQ R15, R15; JGE body` at +0xf76, body +0xd8a
(stores z.ptr → 0x240, z.cap → 0x110, k → 0xe0, yi → 0xb0; THREE `nat.montgomery` calls returning at +0xdef / +0xe6e /
+0xf0c: `zz = zz.mont(z, z)`, `z = z.mont(zz, zz)`, `zz = zz.mont(z, powers[yi >> 62])`; `yi <<= 2`, `k--`, the swap
`z, zz = zz, z`), outer step +0xf80 (`if i == 0 break` → exit +0xf97; `i--`, bounds check `i < len y`, `yi = y[i]`,
`k = 31`, `i` → 0xe8). Loop registers at the test: z = (AX, len in slot 0x148, DX), zz = (R8, R11, R12), BX = m.ptr,
SI = k0, R10 = m.cap, R9 = yi, R15 = k, DI = y.ptr, R13 = y.len, CX = i.
Stack: the callee `RSP` of every montgomery call is `sp - 8`; its stack arguments `m, len m, cap m, k0, n` at
`sp + 0 … sp + 0x28`; the caller's arguments `y` at `sp + 0x278/0x280/0x288`, `m` at `sp + 0x290/0x298/0x2a0`;
`k0` at `sp + 0xd8`; the power table headers at `sp + 0x1b0 + 24 d`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Loop

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2"
/-- the function base -/
abbrev fnE : Nat := segAddr LibW.program fn
/-- the loop test `TESTQ R15, R15` -/
abbrev test : Nat := fnE + 0xf76
/-- the loop exit: the final `zz.montgomery(z, one, …)` -/
abbrev exit : Nat := fnE + 0xf97

/-- the window step of `expNNOddMont 2` (ExpOdd.lean) -/
abbrev step (n Mv k : Nat) (tbl : Nat → Nat) (z d : Nat) : Nat :=
  Exp.montgomery n (Exp.iter (fun z => Exp.montgomery n z z Mv k) 2 z) (tbl d) Mv k

/-- one squaring of the window step -/
abbrev sq (n Mv k z : Nat) : Nat := Exp.montgomery n z z Mv k

theorem step_eq (n Mv k : Nat) (tbl : Nat → Nat) (z d : Nat) :
    step n Mv k tbl z d = Exp.montgomery n (sq n Mv k (sq n Mv k z)) (tbl d) Mv k := rfl

/-- the montgomery callee window `[r - 4288, r + 104)` with `r = sp - 8` -/
abbrev wlo (sp : Nat) : Nat := sp - 4296
abbrev whi (sp : Nat) : Nat := sp + 96

/-- per-array facts of the two Montgomery buffers `z`, `zz` -/
@[reducible] def Buf (R : RtInv) (L : List (Nat × Nat)) (g fs sp n : Nat) (M0 : Memory) (p c : Nat) : Prop :=
  2 * n ≤ c ∧ c < 2 ^ 40 ∧ M0.accessible p (8 * c) true = true ∧ p + 8 * c ≤ 2 ^ 48 ∧
  (InRanges p (8 * c) L ∨ Outside p (8 * c) R.rt) ∧ Apart p (8 * c) (sp - 4296) (4296 + 0x2a8) ∧
  Apart (g + 16) 8 p (8 * c) ∧ Apart (fs - 8) 8 p (8 * c)

/-- a read-only input `p[0:n]` (readable, held, apart from the whole frame `[sp - 4296, sp + 0x2a8)`) -/
@[reducible] def Inp (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧
  Apart p (8 * n) (sp - 4296) (4296 + 0x2a8)

/-- the stack / guard / TLS environment of the loop at the anchor `M0` -/
@[reducible] def Env (R : RtInv) (L : List (Nat × Nat)) (g fs sp : Nat) (M0 : Memory) : Prop :=
  sp % 16 = 0 ∧ 4296 ≤ sp ∧ sp + 0x2a8 ≤ 2 ^ 48 ∧ M0.accessible (sp - 4296) (4296 + 0x2a8) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M0.accessible (g + 16) 8 false = true ∧ M0.readLE (g + 16) 8 + 4296 < sp ∧
  Outside (sp - 4296) (4296 + 0x2a8) R.rt ∧ Apart (g + 16) 8 (sp - 4296) (4296 + 0x2a8) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - 4296, sp + 0x2a8)] ∧
  (8 ≤ fs ∧ fs ≤ 2 ^ 48) ∧ M0.accessible (fs - 8) 8 false = true ∧ M0.readLE (fs - 8) 8 = g ∧
  Apart (fs - 8) 8 (sp - 4296) (4296 + 0x2a8) ∧ Outside (fs - 8) 8 R.rt ∧
  M0.accessible MontHyp.hasADX 1 false = true

set_option maxRecDepth 20000 in
theorem mcall_of {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc rp rc xp yp : Nat} {M0 : Memory}
    (he : Env R L g fs sp M0) (hn : 0 < n) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hr : Buf R L g fs sp n M0 rp rc)
    (hx : Inp R L sp n M0 xp) (hy : Inp R L sp n M0 yp) (hm : Inp R L sp n M0 mp)
    (hrx : Apart rp (8 * rc) xp (8 * n)) (hry : Apart rp (8 * rc) yp (8 * n)) (hrm : Apart rp (8 * rc) mp (8 * n))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8]) :
    MontW.MCall R L g (M0.readLE (g + 16) 8) fs (sp - 8) n mp mc rp rc xp yp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h15, h16, -⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hr
  have sub : ∀ p k, Apart p k (sp - 4296) (4296 + 0x2a8) → Apart p k (sp - 8 - 4288) (4288 + 104) := by
    intro p k h; unfold Apart at h ⊢; omega
  have e : sp - 8 - 4288 = sp - 4296 := by omega
  refine ⟨by omega, by omega, by omega, h5, by omega,
    h8.of_sub (by omega) (by omega), sub _ _ h9, h10, ?_, h12, sub _ _ h15, h16, hn, r1, r2, hmc, hmc', r4, r5,
    sub _ _ r6, r7, r8,
    ⟨hx.2.1, hx.2.2.1, sub _ _ hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, sub _ _ hy.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, hok.1, hok.2⟩
  intro r hr
  have := h11 r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- the static facts of the loop (anchor memory `M0` = the memory at the first arrival at the test) -/
def Static (R : RtInv) (L : List (Nat × Nat)) (g fs sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat)
    (M0 : Memory) : Prop :=
  Env R L g fs sp M0 ∧ 0 < n ∧ n ≤ 2 ^ 16 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧ k0 < 2 ^ 64 ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  Inp R L sp n M0 mp ∧ Inp R L sp ylen M0 yp ∧ M0.readLE yp (8 * ylen) = Y ∧
  (∀ d, d < 4 → Inp R L sp n M0 (pp d) ∧ M0.readLE (pp d) (8 * n) = tbl d ∧ pcap d < 2 ^ 64 ∧
    M0.readLE (sp + 0x1b0 + 24 * d) 8 = pp d ∧ M0.readLE (sp + 0x1b8 + 24 * d) 8 = n ∧
    M0.readLE (sp + 0x1c0 + 24 * d) 8 = pcap d) ∧
  M0.readLE (sp + 0x290) 8 = mp ∧ M0.readLE (sp + 0x298) 8 = n ∧ M0.readLE (sp + 0x2a0) 8 = mc ∧
  M0.readLE (sp + 0xd8) 8 = k0 ∧ M0.readLE (sp + 0x280) 8 = ylen ∧ M0.readLE (sp + 0x278) 8 = yp ∧
  (∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])

/-- the two buffers at a loop state -/
@[reducible] def Bufs (R : RtInv) (L : List (Nat × Nat)) (g fs sp n mp yp ylen : Nat) (pp : Nat → Nat)
    (ext : List (Nat × Nat)) (M0 : Memory) (zp zc zzp zzc : Nat) : Prop :=
  Buf R L g fs sp n M0 zp zc ∧ Buf R L g fs sp n M0 zzp zzc ∧ Apart zp (8 * zc) zzp (8 * zzc) ∧
  Apart zp (8 * zc) mp (8 * n) ∧ Apart zzp (8 * zzc) mp (8 * n) ∧
  Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
  (∀ d, d < 4 → Apart zp (8 * zc) (pp d) (8 * n) ∧ Apart zzp (8 * zzc) (pp d) (8 * n)) ∧
  (∀ q ∈ ext, Apart zp (8 * zc) q.1 q.2 ∧ Apart zzp (8 * zzc) q.1 q.2)

theorem Bufs.swap {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp yp ylen : Nat} {pp : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory} {zp zc zzp zzc : Nat} (h : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) :
    Bufs R L g fs sp n mp yp ylen pp ext M0 zzp zzc zp zc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨a2, a1, a3.symm, a5, a4, a7, a6, fun d hd => ⟨(a8 d hd).2, (a8 d hd).1⟩,
    fun q hq => ⟨(a9 q hq).2, (a9 q hq).1⟩⟩

/-- the frame ranges the loop writes (callee window + spills), without the two buffers -/
@[reducible] def fw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xb8), (sp + 0xe0, sp + 0xf0), (sp + 0x110, sp + 0x118),
    (sp + 0x140, sp + 0x150), (sp + 0x190, sp + 0x198), (sp + 0x240, sp + 0x248), (sp + 0x258, sp + 0x260)]

/-- everything the loop may change since the anchor `M0` -/
@[reducible] def lw (R : RtInv) (sp zp zc zzp zzc : Nat) : List (Nat × Nat) :=
  R.rt ++ fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]

/-- the frame facts of a loop state since the anchor `M0` -/
@[reducible] def FL (R : RtInv) (L : List (Nat × Nat)) (sp zp zc zzp zzc : Nat) (M0 M : Memory) : Prop :=
  MemFrame M0 M (lw R sp zp zc zzp zzc) ∧ LiveFrame M0 M L [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]

/-- the memory facts at a loop state `M` -/
@[reducible] def Mem (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M0 M : Memory) (zp zc zzp zzc : Nat) :
    Prop :=
  FL R L sp zp zc zzp zzc M0 M ∧ R.inv b L g (view R.rt L M) ∧ M.regions = M0.regions

theorem FL.write {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M : Memory}
    (h : FL R L sp zp zc zzp zzc M0 M) (hLs : LiveSep L [(sp - 4296, sp + 0x2a8)]) {a k : Nat} (v : Nat)
    (hw : ∃ r ∈ fw sp, r.1 ≤ a ∧ a + k ≤ r.2) (hs : 4296 ≤ sp) :
    FL R L sp zp zc zzp zzc M0 (M.writeLE a k v) := by
  obtain ⟨r, hr, h1, h2⟩ := hw
  have hr' : sp - 4296 ≤ r.1 ∧ r.2 ≤ sp + 0x2a8 := by
    simp only [fw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  refine ⟨h.1.writeLE_inRanges v ⟨r, by simp only [lw, List.mem_append]; exact Or.inl (Or.inr hr), h1, h2⟩,
    h.2.writeLE v (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))⟩

theorem FL.call {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M M' : Memory} {rp rc : Nat}
    (h : FL R L sp zp zc zzp zzc M0 M)
    (hc : MemFrame M M' (R.rt ++ [(sp - 8 - 4288, sp - 8 + 104)] ++ [(rp, rp + 8 * rc)]))
    (hl : LiveFrame M M' L [(rp, rp + 8 * rc)]) (hr : (rp = zp ∧ rc = zc) ∨ (rp = zzp ∧ rc = zzc)) (hs : 4296 ≤ sp) :
    FL R L sp zp zc zzp zzc M0 M' := by
  refine ⟨h.1.trans hc (fun a n ho => ⟨ho, ?_⟩),
    h.2.trans (FvModexp.Expmc.liveFrame_widen hl (fun a n ho => ?_)) (fun _ _ h => h)⟩
  · simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 e2 <;> omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 e2 <;> omega

theorem FL.swap {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M : Memory}
    (h : FL R L sp zp zc zzp zzc M0 M) : FL R L sp zzp zzc zp zc M0 M := by
  refine ⟨(MemFrame.refl M0 []).trans h.1 (fun a n ho => ⟨trivial, ?_⟩),
    FvModexp.Expmc.liveFrame_widen h.2 (fun a n ho => ?_)⟩
  · simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    exact ⟨ho.1, by omega⟩
  · simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega

/-- a held input outside the loop's frame and buffers reads as at the anchor -/
theorem FL.read {R : RtInv} {L : List (Nat × Nat)} {sp zp zc zzp zzc : Nat} {M0 M : Memory} {a n : Nat}
    (h : FL R L sp zp zc zzp zzc M0 M) (hh : InRanges a n L ∨ Outside a n R.rt)
    (h1 : Apart a n (sp - 4296) (4296 + 0x2a8)) (hs : 4296 ≤ sp) (h2 : Apart zp (8 * zc) a n)
    (h3 : Apart zzp (8 * zzc) a n) : M.readLE a n = M0.readLE a n := by
  unfold Apart at h1 h2 h3
  exact FvModexp.Expmc.held_readLE hh h.1 h.2 (by simp only [fw, outside_cons, outside_nil, and_true]; omega)
    (by simp only [outside_cons, outside_nil, and_true]; omega)

theorem outer_succ (st : Nat → Nat → Nat) (Y i yi c z : Nat) :
    Exp.outerLoop 2 st Y 32 i yi (c + 1) z =
      Exp.outerLoop 2 st Y 32 i ((yi * 2 ^ 2) % Exp.B) c (st z (yi / 2 ^ (64 - 2))) := by
  cases i <;> rfl

theorem outer_zero (st : Nat → Nat → Nat) (Y i yi z : Nat) :
    Exp.outerLoop 2 st Y 32 (i + 1) yi 0 z = Exp.outerLoop 2 st Y 32 i (Exp.wd Y i) 32 z := rfl

theorem outer_done (st : Nat → Nat → Nat) (Y yi z : Nat) : Exp.outerLoop 2 st Y 32 0 yi 0 z = z := rfl

end FvModexp.Amd64.W2Loop
