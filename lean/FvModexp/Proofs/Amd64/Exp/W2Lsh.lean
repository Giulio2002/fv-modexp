import FvModexp.Proofs.Amd64.Exp.W2Sn2R
import FvModexp.Proofs.Amd64.Nat.LshDefs

set_option autoImplicit false

/-!
# window-2 prologue (amd64): the call `zz := nat(nil).lsh(RR, 2·n·_W)` (nat.go:1398), `lshE → lshRet`
(agent expmc s53; twin of `Arm64.W2Lsh`)

`nat.lsh` is a premise in the `Lsh.Hyp2` shape (asm proves it), parametric in its names `nsL` and stack bound
`stkL ≤ K`; its spill bound is `64`. Arguments: `z = nil` (`AX = BX = CX = 0`), `x = RR[0:1]` (`DI` pointer, `SI = 1`,
`R8` = cap `2n`), `R9 = sh = 128 n`. Return address `lshRet` = fn+0x585 at `[sp - 8]`. The result is a FRESH nat.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W2Pro

/-- entry of `nat.lsh` -/
abbrev lshE : Nat := 6186528

theorem lshE_eq : segAddr Extracted.program Lsh.fn = lshE := by decide

/-- the facts at the `lsh` call (memory form; `sp` = window-2's `RSP`) -/
@[reducible] def LsPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp K stkL rrp n : Nat) (M : Memory) :
    Prop :=
  CallW.CEnv R L g fs (sp - 8) K 688 M ∧ stkL ≤ K ∧ RunIface.Serves R ∧ n ≤ 128 ∧ 0 < n ∧
  M.accessible rrp (8 * 1) false = true ∧ rrp + 8 * 1 ≤ 2 ^ 48 ∧ Held R L rrp (8 * 1) ∧ AWx sp K rrp (8 * 1) ∧
  makeCost (1 + 128 * n / 64 + 1) ≤ b ∧ R.inv b L g (view R.rt L M)

/-- the callee's post (memory form) -/
@[reducible] def LsPost (R : RtInv) (b : Nat) (L L' : List (Nat × Nat)) (b' g sp stkL rrp n : Nat) (M M' : Memory)
    (p l c : Nat) : Prop :=
  EvenHyp.NatRes R L L' M' 0 0 (1 + 128 * n / 64 + 1) p l c (natVal M rrp 1 * 2 ^ (128 * n)) ∧
  (0 < 1 + 128 * n / 64 + 1 → 1 + 128 * n / 64 + 1 ≤ c) ∧
  LiveExt R L L' ∧ b - makeCost (1 + 128 * n / 64 + 1) ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧
  MemFrame M M' (R.rt ++ [(sp - 8 - stkL, sp - 8 + 64)] ++ [(0, 0 + 8 * 0)]) ∧
  LiveFrame M M' L [(0, 0 + 8 * 0)] ∧ M'.regions = M.regions

theorem out_winL {sp K stk a k : Nat} (hKD : stk ≤ K) (h : AWx sp K a k) :
    Outside a k [(sp - 8 - stk, sp - 8 + 64)] := by
  simp only [AWx, Apart] at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- `LsPre` at the call state gives `nat.lsh`'s precondition -/
theorem ls_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g fs sp K stkL rrp n : Nat} {S : State}
    (hpre : LsPre R b L g fs sp K stkL rrp n S.mem) (hrrp : rrp < 2 ^ 64)
    (tsp : (S.regs 4).toNat = sp - 8) (tg : (S.regs 14).toNat = g) (hfs : S.fsBase.toNat = fs) :
    Lsh.LshPreA R b L stkL 64 (BitVec.ofNat 64 0).toNat (BitVec.ofNat 64 0).toNat (BitVec.ofNat 64 0).toNat
      (BitVec.ofNat 64 rrp).toNat (BitVec.ofNat 64 1).toNat (BitVec.ofNat 64 (128 * n)).toNat S ∧
      0 < (BitVec.ofNat 64 (128 * n)).toNat ∧ 0 < (BitVec.ofNat 64 1).toNat := by
  obtain ⟨hce, hKL, hserv, hn128, hn, hra, hr48, hrH, hrW, hcost, hinv⟩ := hpre
  have hK : K ≤ sp - 8 := hce.2.1
  have t0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
  have t1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have t3 := MontW.toNat_of hrrp
  have t6 : (BitVec.ofNat 64 (128 * n)).toNat = 128 * n := MontW.toNat_of (by omega)
  rw [t0, t1, t3, t6]
  have hce' := CallW.callEnv_of hce tsp tg hfs rfl (stk := stkL) (above := 64) hKL (by omega) (by omega)
  simp only [Lsh.LshPreA, EvenHyp.WrOut, EvenHyp.RdIn, win, tsp, tg]
  exact ⟨⟨hce', hserv, Nat.le_refl _, ⟨by decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
    ⟨by decide, hra, hr48, hrH, out_winL hKL hrW⟩, by omega, Or.inr fun h => absurd h (by decide), hcost, hinv⟩,
    by omega, by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.lsh` from its entry (return address `lshRet` at `[sp - 8]`) to `lshRet` -/
theorem lshCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsW : nsL.contains W2Loop.fn = false)
    {ret : W64} {Q : State → Prop} {b : Nat} {L : List (Nat × Nat)} {g fs sp K rrp n : Nat} {r5 : W64}
    (S : State) (hpre : LsPre R b L g fs sp K stkL rrp n S.mem) (hrrp : rrp < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 lshE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hrd : S.mem.readLE (sp - 8) 8 = lshRet)
    (h0 : S.regs 0 = BitVec.ofNat 64 0) (h3 : S.regs 3 = BitVec.ofNat 64 0) (h1 : S.regs 1 = BitVec.ofNat 64 0)
    (h7 : S.regs 7 = BitVec.ofNat 64 rrp) (h6 : S.regs 6 = BitVec.ofNat 64 1) (h8 : S.regs 8 = BitVec.ofNat 64 (2 * n))
    (h9 : S.regs 9 = BitVec.ofNat 64 (128 * n))
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KB : ∀ (S' : State) (L' : List (Nat × Nat)) (b' p l c : Nat),
      S'.rip = BitVec.ofNat 64 lshRet → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 3 = BitVec.ofNat 64 l → S'.regs 1 = BitVec.ofNat 64 c →
      LsPost R b L L' b' g sp stkL rrp n S.mem S'.mem p l c →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hn128 : n ≤ 128 := hpre.2.2.2.1
  have hK : K ≤ sp - 8 := hpre.1.2.1
  have hA : sp - 8 + 688 ≤ 2 ^ 48 := hpre.1.2.2.1
  have hg1 : g + 24 ≤ 2 ^ 48 := hpre.1.2.2.2.2.1
  have hc : CodeIn64 ((Extracted.program.onlySegments nsL).link impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact A64.codeIn_restrict_mono64 hap hnsL
  have hS := Ensures.toSummaryIn (hLsh b L (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 rrp) (BitVec.ofNat 64 1) (BitVec.ofNat 64 (2 * n)) (BitVec.ofNat 64 (128 * n)))
    (A64.noExit_restrict64 hap nsL) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide) hc
  rw [lshE_eq] at hS
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tg : (S.regs 14).toNat = g := by rw [h14]; exact MontW.toNat_of (by omega)
  refine ReachesRet.call_regions hS hpc ⟨?ra, hx15, ?args, hdf, ls_pre hpre hrrp tsp tg hfs⟩
    (fun s' hr ⟨⟨e4, e5, e14, ex15⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [tsp, hrd]; exact W2Loop.ra_of hap hnsW 0x585 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨h0, h3, h1, h7, h6, h8, h9, trivial⟩
  have t0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
  have t1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have t3 := MontW.toNat_of hrrp
  have t6 : (BitVec.ofNat 64 (128 * n)).toNat = 128 * n := MontW.toNat_of (by omega)
  obtain ⟨efs, edf, p, l, c, hX0, hX3, hX1, L', b', hres, hcap, ⟨hLE, hb', hinv'⟩, hF, hLF⟩ := hq
  simp only [t0, t1, t3, t6] at hres hcap hb' hF hLF
  rw [tg] at hinv'
  simp only [win, tsp] at hF
  exact KB s' L' b' p l c (by rw [hr, retAddrOf_eq, tsp, hrd])
    (by rw [e4, hsp]; exact W2Loop.sp_add8 (by omega) (by omega)) (e5.trans h5) (e14.trans h14) (by rw [efs, hfs])
    (by rw [ex15, hx15]) (by rw [edf, hdf]) hX0 hX3 hX1 ⟨hres, hcap, hLE, hb', hinv', hF, hLF, hrg⟩

end FvModexp.Amd64.W2Pro
