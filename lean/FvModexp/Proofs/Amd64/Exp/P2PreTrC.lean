import FvModexp.Proofs.Amd64.Exp.P2PreRS0
import FvModexp.Proofs.Amd64.Nat.TruncDefs
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `nat.trunc` call helpers (agent divmc s64; twin of infra's
`Arm64/Exp/P2PreTr` / `P2PreCall` (`bufArr`) / `LibCalls.truncCall`)

`truncCallP`: a call of `Trunc.Hyp2` at its entry `6188320` (adapted from infra's `Amd64/Exp/SubMod2NGC.truncCallW`,
the continuation also gets `RBP` kept). `bufArr`: an array inside `buf` as a callee operand / result (`WrOut`,
`RdIn`). `len_le_w`, `makeCost_le`, `effL`: arithmetic of the result length and the budget.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep)

theorem trunc_addr : segAddr Extracted.program Trunc.fn = 6188320 := by decide

theorem makeCost_le {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

/-- a normalised nat below `2^lm` has at most `w = ⌈lm/64⌉` words -/
theorem len_le_w {m : Memory} {p l lm : Nat} (hn : NatNorm m p l) (hv : natVal m p l < 2 ^ lm) : l ≤ W lm := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · omega
  have h1 := SubMod2N.natVal_lower m p l hn h0
  have : 64 * (l - 1) < lm := (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt h1 hv)
  simp only [W]; omega

/-- the effective budget after a callee that keeps the stack capacity (`r' = r`), charged `c ≤ b1` (as infra's
`Arm64/Exp/P2Q.effL`) -/
theorem effL {R : RtInv} {b1 c r r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b1 + r - c ≤ b') (hc : c ≤ b1) (hr : r' = r) : ∃ b2, R.inv (b2 + r') L g v ∧ b1 - c ≤ b2 :=
  ⟨b' - r, by rw [hr, Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

theorem p2_one {lm X : Nat} : Exp.p2Pow lm X 1 = X % 2 ^ lm := by rw [Exp.p2Pow]; simp

set_option maxRecDepth 20000 in
/-- a call of `nat.trunc` (`Trunc.Hyp2`) at its entry, continuation over the callee's postcondition -/
theorem truncCallP {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (htr : Trunc.Hyp2 impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6188320) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bn : n < 2 ^ 64)
    (hpre : TruncPre R b L stk above zp zl zc x xl n S) (hnorm : NatNorm S.mem x xl ∨ (n + 63) / 64 ≤ xl)
    (hcp : zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      TruncPost R b L stk above zp zc x xl n S s' → ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n))
  rw [trunc_addr] at hS
  have hzl : zl < 2 ^ 64 := by have := hpre.2.2.1; omega
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN hzl, tN bzc, tN bx, tN bxl, tN bn]; exact ⟨hpre, hnorm, hcp⟩
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bn] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

section
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- an array `[a, a + 8 c)` inside `buf` as a callee operand / result at `S'` (`RSP_c = RSP - 184`) -/
theorem bufArr (hpre : Pre R kc b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) (hf : PF R kc L st pw pl s)
    {S' : State} (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) (h14 : S'.regs 14 = s.regs 14)
    (hfs : S'.fsBase = s.fsBase) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {a c : Nat} (h1 : bp ≤ a)
    (h2 : a + 8 * c ≤ bp + 8 * NB pl lm) (h0 : 0 < c) (hal : a % 8 = 0) (hc40 : c < 2 ^ 40) :
    WrOut R L1 S' stk above a c ∧ (∀ l, l ≤ c → RdIn R L1 S' stk above a l) := by
  obtain ⟨⟨-, -, -, -, -, -, hgrt, -, -, -, htrt, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, -, -, -, hfg, -, -, -, -, -, -, -, -, hft⟩, -⟩ := hpre
  have hwok := wok_buf (zp := a) (zn := 8 * c) hc.scr h1 h2
  have hwin := wok_win hwok hf.w (by simp only; omega)
  have hK := hf.w.sp
  simp only [K, A] at hwin hK
  have hacc : M.accessible a (8 * c) true = true := Janus.Arm64.Memory.accessible_mono _ hc.scr.acc h1 (by omega)
  have hheld : Held R L1 a (8 * c) := hc.scr.held.sub h1 h2
  have hb48 : a + 8 * c ≤ 2 ^ 48 := by have := hc.scr.b48; omega
  have hgt : Apart a (8 * c) ((s.regs 14).toNat + 16) 8 ∧ Apart a (8 * c) (s.fsBase.toNat - 8) 8 := by
    simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN, Q.NatSqr.guard, Q.NatSqr.tls] at hfg hft
    rcases hc.scr.loc with ⟨-, l1, l2⟩ | ⟨hin, -⟩
    · unfold Apart at hfg hft ⊢; omega
    · have e1 := (hin.sub (a := a) (n := 8 * c) h1 (by omega)).apart hgrt
      have e2 := (hin.sub (a := a) (n := 8 * c) h1 (by omega)).apart htrt
      unfold Apart at e1 e2 ⊢; omega
  subst hm
  refine ⟨⟨hc40, fun _ => ⟨hal, hheld, hacc, hb48⟩, fun _ => ⟨?_, by rw [h14]; exact hgt.1, by rw [hfs]; exact hgt.2⟩⟩,
    fun l hl => ⟨by omega, Janus.Arm64.Memory.accessible_weaken _
      (Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)), by omega,
      hheld.sub (Nat.le_refl _) (by omega), ?_⟩⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

end

end FvModexp.Amd64.P2Pre
