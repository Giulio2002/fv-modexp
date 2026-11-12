import FvModexp.Proofs.Arm64.Exp.W2Sn2R
import FvModexp.Proofs.Arm64.Nat.LshDefs

/-!
# window-2 prologue (arm64): the call `zz := nat(nil).lsh(RR, 2·n·_W)` (nat.go:1398), `lshE → lshRet`

`nat.lsh` is a premise in expmc's `ExpHyp.LshHyp` shape (asm proves it), parametric in its names `nsL` and stack bound
`stkL ≤ K`; its spill bound is `64` (7 register arguments). Arguments: `z = nil` (`0, 0, 0`), `x = RR[0:1]`
(pointer, len 1, cap `2n`), `sh = 128 n`. The result is a FRESH nat (`cap z = 0 < need`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

/-- entry of `nat.lsh` -/
abbrev lshE : Nat := 1784560

/-- the facts at the `lsh` call (memory form) -/
@[reducible] def LsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp K stkL rrp n : Nat) (M : Memory) : Prop :=
  CallW.CEnv R L g sp K 752 M ∧ stkL ≤ K ∧ RunIface.Serves R ∧ n ≤ 128 ∧ 0 < n ∧
  M.accessible rrp (8 * 1) false = true ∧ rrp + 8 * 1 ≤ 2 ^ 48 ∧ Held R L rrp (8 * 1) ∧ AW sp K rrp (8 * 1) ∧
  makeCost (1 + 128 * n / 64 + 1) ≤ b ∧ R.inv b L g (view R.rt L M)

/-- the callee's post (memory form) -/
@[reducible] def LsPost (R : RtInv) (b : Nat) (L L' : List (Nat × Nat)) (b' g sp stkL rrp n : Nat) (M M' : Memory)
    (p l c : Nat) : Prop :=
  ExpHyp.NatRes R L L' M' 0 0 (1 + 128 * n / 64 + 1) p l c (natVal M rrp 1 * 2 ^ (128 * n)) ∧
  (0 < 1 + 128 * n / 64 + 1 → 1 + 128 * n / 64 + 1 ≤ c) ∧
  LiveExt R L L' ∧ b - makeCost (1 + 128 * n / 64 + 1) ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧
  MemFrame M M' (R.rt ++ [(sp - stkL, sp - 8), (sp + 8, sp + 64)] ++ [(0, 0 + 8 * 0)]) ∧
  LiveFrame M M' L [(0, 0 + 8 * 0)] ∧ M'.regions = M.regions

theorem out_win' {sp K stk a k : Nat} (hKD : stk ≤ K) (h : AW sp K a k) :
    Outside a k [(sp - stk, sp + 64)] := by
  simp only [AW, Apart] at h; simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `nat.lsh` from its entry (return address `lshRet`) to `lshRet` -/
theorem lshCallK (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibExp.names.contains x = true)
    (hnsW : nsL.contains Extracted.seg35.name = false)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp K rrp n : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (hpre : LsPre R b L g sp K stkL rrp n M) (hrrp : rrp < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 lshE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 0) (h1 : S.regs 1 = BitVec.ofNat 64 0) (h2 : S.regs 2 = BitVec.ofNat 64 0)
    (h3 : S.regs 3 = BitVec.ofNat 64 rrp) (h4 : S.regs 4 = BitVec.ofNat 64 1) (h5 : S.regs 5 = BitVec.ofNat 64 (2 * n))
    (h6 : S.regs 6 = BitVec.ofNat 64 (128 * n)) (h30 : S.regs 30 = BitVec.ofNat 64 lshRet)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KB : ∀ (S' : State) (M' : Memory) (L' : List (Nat × Nat)) (b' p l c : Nat),
      S'.pc = BitVec.ofNat 64 lshRet → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 1 = BitVec.ofNat 64 l → S'.regs 2 = BitVec.ofNat 64 c →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      LsPost R b L L' b' g sp stkL rrp n M M' p l c →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨hce, hKL, hserv, hn128, hn, hra, hr48, hrH, hrW, hcost, hinv⟩ := hpre
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hS0 := CallW.hypSum hap hnsL (hLsh b L (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 rrp) (BitVec.ofNat 64 1) (BitVec.ofNat 64 (2 * n)) (BitVec.ofNat 64 (128 * n)))
  rw [show segAddr Extracted.program Lsh.fn = lshE by decide] at hS0
  have t0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
  have t1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have t3 := toNat_lt' hrrp
  have t6 : (BitVec.ofNat 64 (128 * n)).toNat = 128 * n := toNat_lt' (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt' (by omega)
  have tg : (S.regs 28).toNat = g := by rw [h28]; exact toNat_lt' (by omega)
  refine Reaches.call_regions (hS0.withExit hret) hpc ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [h30, toNat_lt' (by decide)]
    exact CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := nsL)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hnsW 246
      (by decide) (by decide) (by decide)
  case args =>
    simp only [ArgsFrom]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  case pre =>
    simp only [EvenHyp.LshPreA, ExpHyp.WrOut, ExpHyp.RdIn]
    rw [t0, t1, t3, t6, hmem]
    have hce' := CallW.callEnv_of hce hsp h28 hmem (stk := stkL) (above := 64) hKL (by omega)
    simp only [win, tsp, tg]
    refine ⟨⟨hce', hserv, Nat.le_refl _, ⟨by decide, by simp, fun h => absurd h (by decide)⟩,
      ⟨by decide, hra, hr48, hrH, out_win' hKL hrW⟩, by omega, Or.inr fun h => absurd h (by decide), hcost, hinv⟩,
      by omega, by decide⟩
  obtain ⟨p, l, c, hX0, hX1, hX2, L', b', hres, hcap, ⟨hLE, hb', hinv'⟩, hF, hLF⟩ := hq
  simp only [t0, t1, t3, t6, hmem, tsp, tg, winA] at hres hcap hb' hinv' hF hLF
  refine KB s' s'.mem L' b' p l c (hr.trans h30) (e1.trans hsp) hX0 hX1 hX2 (e4.trans h18) (e2.trans h28)
    (e3.trans h29) rfl ⟨hres, hcap, hLE, hb', hinv', hF, hLF, by rw [hrg, hmem]⟩

end FvModexp.Arm64.W2Pro
