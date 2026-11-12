import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W2Ctx
import FvModexp.Proofs.Arm64.Exp.W2RR

/-!
# window-2 prologue (arm64): the call `_, RR = nat(stk.nat(2n)).div(stk, RR, zz, m)` (nat.go:1399), `divE → divRet`

`nat.div` is a premise in expmc's `ExpHyp.DivHyp` shape (asm proves it), parametric in its names `nsD`, its stack bound
`stkD ≤ K` and its closed cost `costD`; its spill bound is `112` (13 register arguments). The call is made by hand
(`Reaches.call_regions` + `LibWC.hypSum`, return address `divRet` = seg35 word ?). Arguments: `z` = the fresh
stack nat `q` (`2n` words), `z2` = `RR` (pointer, len 1, cap `2n`), `u` = `zz` (`2^(128n)`), `v` = `m`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

/-- entry of `nat.div` -/
abbrev divE : Nat := 1806848

/-- the facts at the `div` call (memory form; the callee window is `[sp - stkD, sp + 112)`, inside the frame's) -/
@[reducible] def DvPre (R : RtInv) (b : Nat) (costF : Nat → Nat → Nat → Nat) (cost : Nat) (L : List (Nat × Nat)) (g sp K stkD st qp rrp n zzp zzl mp : Nat)
    (M : Memory) : Prop :=
  CallW.CEnv R L g sp K 752 M ∧ stkD ≤ K ∧ RunIface.Serves R ∧ RunIface.Globals R M [(sp - K, sp + 752)] ∧ n ≤ 128 ∧ 0 < n ∧
  NatLive M R L qp (2 * n) ∧ AW sp K qp (8 * (2 * n)) ∧ Apart qp (8 * (2 * n)) (g + 16) 8 ∧
  NatLive M R L rrp (2 * n) ∧ AW sp K rrp (8 * (2 * n)) ∧ Apart rrp (8 * (2 * n)) (g + 16) 8 ∧
  zzl ≤ 2 ^ 9 ∧ M.accessible zzp (8 * zzl) false = true ∧ zzp + 8 * zzl ≤ 2 ^ 48 ∧ Held R L zzp (8 * zzl) ∧
  AW sp K zzp (8 * zzl) ∧
  M.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧ Held R L mp (8 * n) ∧ AW sp K mp (8 * n) ∧
  NatNorm M zzp zzl ∧ NatNorm M mp n ∧
  StkOK M R L st ∧ AW sp K st 24 ∧
  (0 < stCap M st → AW sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  stLen M st + 16 * zzl + 64 ≤ 2 ^ 16 ∧ 0 < stCap M st ∧
  Apart zzp (8 * zzl) st 24 ∧ Apart zzp (8 * zzl) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) ∧
  Apart mp (8 * n) st 24 ∧ Apart mp (8 * n) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) ∧
  Apart qp (8 * (2 * n)) rrp (8 * (2 * n)) ∧
  (∀ p, p = qp ∨ p = rrp → Apart p (8 * (2 * n)) zzp (8 * zzl) ∧ Apart p (8 * (2 * n)) mp (8 * n) ∧
    Apart p (8 * (2 * n)) st 24 ∧
    Apart p (8 * (2 * n)) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))) ∧
  Apart qp (8 * (2 * n)) RunIface.gA 32 ∧ Apart rrp (8 * (2 * n)) RunIface.gA 32 ∧ Apart st 24 RunIface.gA 32 ∧
  Apart (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) RunIface.gA 32 ∧
  costF (stLen M st) zzl n ≤ cost ∧ cost ≤ b ∧ R.inv b L g (view R.rt L M)

theorem out_win {sp K stkD a k : Nat} (hKD : stkD ≤ K) (h : AW sp K a k) :
    Outside a k [(sp - stkD, sp + 112)] := by
  simp only [AW, Apart] at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the callee's post about the remainder and the memory (memory form) -/
@[reducible] def DvPost (R : RtInv) (b cost : Nat) (L L' : List (Nat × Nat)) (b' g sp stkD st qp rrp n zzp zzl mp : Nat)
    (M M' : Memory) (r rl rc : Nat) : Prop :=
  ExpHyp.NatOF R L L' M' rrp (2 * n) 1 r rl rc (natVal M zzp zzl % natVal M mp n) ∧
  LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧ StackBack R L L' st M M' ∧
  (¬ (r = rrp ∧ rc = 2 * n) → 0 < rc → 0 < stCap M' st → Apart r (8 * rc) (stW M' st) (8 * stCap M' st)) ∧
  MemFrame M M' (R.rt ++ [(sp - stkD, sp - 8), (sp + 8, sp + 112)] ++ [(qp, qp + 8 * (2 * n)), (rrp, rrp + 8 * (2 * n))] ++
    stkWs M st) ∧
  LiveFrame M M' L ([(qp, qp + 8 * (2 * n)), (rrp, rrp + 8 * (2 * n))] ++ stkWs M st) ∧ M'.regions = M.regions

/-- move a division-cost bound to an equal stack level -/
theorem cf_eq {f : Nat → Nat → Nat → Nat} {a b u v c : Nat} (h : f a u v ≤ c) (e : b = a) : f b u v ≤ c := e ▸ h

theorem globals_win {R : RtInv} {M : Memory} {sp K stkD : Nat} (h : RunIface.Globals R M [(sp - K, sp + 752)])
    (hKD : stkD ≤ K) : RunIface.Globals R M [(sp - stkD, sp + 112)] := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := h
  simp only [outside_cons, outside_nil, and_true] at g10 g13
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, by simp only [outside_cons, outside_nil, and_true]; omega, g11, g12,
    by simp only [outside_cons, outside_nil, and_true]; omega⟩

theorem globals_nil {R : RtInv} {M : Memory} {w : List (Nat × Nat)} (h : RunIface.Globals R M w) :
    RunIface.Globals R M := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, -, g11, g12, -⟩ := h
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, by rw [outside_nil]; trivial, g11, g12, by rw [outside_nil]; trivial⟩

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `nat.div` from its entry (return address `divRet`) to `divRet` -/
theorem divCallK (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp K st qp rrp n zzp zzl zzc mp mc : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (hpre : DvPre R b costF costD L g sp K stkD st qp rrp n zzp zzl mp M)
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hrrp : rrp < 2 ^ 64) (hzzp : zzp < 2 ^ 64) (hzzc : zzc < 2 ^ 64)
    (hmp : mp < 2 ^ 64) (hmc : mc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n)) (h3 : S.regs 3 = BitVec.ofNat 64 st)
    (h4 : S.regs 4 = BitVec.ofNat 64 rrp) (h5 : S.regs 5 = BitVec.ofNat 64 1) (h6 : S.regs 6 = BitVec.ofNat 64 (2 * n))
    (h7 : S.regs 7 = BitVec.ofNat 64 zzp) (h8 : S.regs 8 = BitVec.ofNat 64 zzl) (h9 : S.regs 9 = BitVec.ofNat 64 zzc)
    (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h12 : S.regs 12 = BitVec.ofNat 64 mc) (h30 : S.regs 30 = BitVec.ofNat 64 divRet)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KB : ∀ (S' : State) (M' : Memory) (L' : List (Nat × Nat)) (b' r rl rc : Nat),
      S'.pc = BitVec.ofNat 64 divRet → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 r → S'.regs 4 = BitVec.ofNat 64 rl → S'.regs 5 = BitVec.ofNat 64 rc →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      DvPost R b costD L L' b' g sp stkD st qp rrp n zzp zzl mp M M' r rl rc →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  obtain ⟨hce, hKD, hserv, hgl, hn128, hn, hqL, hqW, hqG, hrL, hrW, hrG, hzl, hza, hz48, hzH, hzW, hma, hm48, hmH, hmW,
    hzN, hmN, hsok, hstW, harr, hslen, hcap, huH, huF, hvH, hvF, hqr, hpair, hgq, hgz, hgst, hgfr, hcF, hcost, hinv⟩ := hpre
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hS0 := LibWC.hypSum hap hnsD (hDiv b L (BitVec.ofNat 64 qp) (BitVec.ofNat 64 (2 * n)) (BitVec.ofNat 64 (2 * n))
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 rrp) (BitVec.ofNat 64 1) (BitVec.ofNat 64 (2 * n)) (BitVec.ofNat 64 zzp)
    (BitVec.ofNat 64 zzl) (BitVec.ofNat 64 zzc) (BitVec.ofNat 64 mp) (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc))
  rw [show segAddr Extracted.program ExpHyp.fnDiv = divE by decide] at hS0
  have t0 := toNat_lt' hqp
  have t1 : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := toNat_lt' (by omega)
  have t3 := toNat_lt' hst
  have t4 := toNat_lt' hrrp
  have t5 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have t7 := toNat_lt' hzzp
  have t8 : (BitVec.ofNat 64 zzl).toNat = zzl := toNat_lt' (by omega)
  have t10 := toNat_lt' hmp
  have t11 : (BitVec.ofNat 64 n).toNat = n := toNat_lt' (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt' (by omega)
  have tg : (S.regs 28).toNat = g := by rw [h28]; exact toNat_lt' (by omega)
  refine Reaches.call_regions (hS0.withExit hret) hpc ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [h30, toNat_lt' (by decide)]
    exact CallW.retAddr_restrict hap (cs := Extracted.seg35) (ns := nsD)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hnsW 263
      (by decide) (by decide) (by decide)
  case args =>
    simp only [ArgsFrom]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, trivial⟩
  case pre =>
    simp only [ExpHyp.DivPre, ExpHyp.WrOut, ExpHyp.RdIn, ExpHyp.StackOK']
    rw [t0, t1, t3, t4, t5, t7, t8, t10, t11, hmem]
    have hce' := CallW.callEnv_of hce hsp h28 hmem (stk := stkD) (above := 112) hKD (by omega)
    simp only [win, tsp, tg]
    refine ⟨hce', hserv, globals_win hgl hKD, Nat.le_refl _, by omega,
      ⟨by omega, hqL, fun _ => ⟨out_win hKD hqW, hqG⟩⟩, ⟨by omega, hrL, fun _ => ⟨out_win hKD hrW, hrG⟩⟩,
      ⟨by omega, hza, hz48, hzH, out_win hKD hzW⟩, ⟨by omega, hma, hm48, hmH, out_win hKD hmW⟩, hzl, hn, by omega,
      hzN, hmN, hsok, out_win hKD hstW, fun hc => ⟨out_win hKD (harr hc).1, (harr hc).2⟩, hslen,
      fun h => absurd h (by omega), huH, huF, hvH, hvF,
      fun _ => hgq, fun _ => hgz, hgst, hgfr,
      fun _ _ => hqr, fun p c hpc' _ => ?_, Nat.le_trans hcF hcost, hinv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpc'
    rcases hpc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hpair _ (Or.inl rfl)
    · exact hpair _ (Or.inr rfl)
  obtain ⟨q, ql, qc, r, rl, rc, hX0, hX1, hX2, hX3, hX4, hX5, L', b', hqOF, hrOF, ⟨hLE, hb', hinv'⟩, hsb, hfr, hF, hLF⟩ :=
    hq
  simp only [t0, t1, t3, t4, t7, t8, t10, t11, hmem, tsp, tg, winA] at hqOF hrOF hb' hinv' hsb hfr hF hLF
  refine KB s' s'.mem L' b' r rl rc (hr.trans h30) (e1.trans hsp) hX3 hX4 hX5 (e4.trans h18) (e2.trans h28)
    (e3.trans h29) rfl ⟨hrOF, hLE, by omega, hinv', hsb, hfr, hF, hLF, by rw [hrg, hmem]⟩

end FvModexp.Arm64.W2Pro
