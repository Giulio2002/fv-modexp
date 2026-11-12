import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W4CtxB
import FvModexp.Proofs.Arm64.Exp.W4Div

/-!
# window-4 prologue (arm64): a general `nat.div` call `q, r = z.div(stk, z2, u, m)` (`divCallG`)

Generalisation of `divCallK` (W4Div) to any `z = (qp, ql, qc)`, `z2 = (z2p, z2l, z2c)`, `u = (up, ul, uc)` and any return
address `ra` of window-4 (word `i` of seg34); used by the `x` normalisation (nat.go:1378, `x mod m`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

/-- a written argument nat of the `div` call (memory form) -/
@[reducible] def DvOut (R : RtInv) (L : List (Nat × Nat)) (g sp K : Nat) (M : Memory) (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L p c ∧ (0 < c → AW sp K p (8 * c) ∧ Apart p (8 * c) (g + 16) 8)

/-- the facts at a general `div` call (memory form; the callee window is `[sp - stkD, sp + 112)`) -/
@[reducible] def DvPreG (R : RtInv) (b : Nat) (costF : Nat → Nat → Nat → Nat) (cost : Nat) (L : List (Nat × Nat)) (g sp K stkD st qp ql qc z2p z2l z2c up ul mp n : Nat)
    (M : Memory) : Prop :=
  CallW.CEnv R L g sp K 1040 M ∧ stkD ≤ K ∧ RunIface.Serves R ∧ RunIface.Globals R M [(sp - K, sp + 1040)] ∧ n ≤ 128 ∧ 0 < n ∧
  ql ≤ qc ∧ z2l ≤ z2c ∧ DvOut R L g sp K M qp qc ∧ DvOut R L g sp K M z2p z2c ∧
  ul ≤ 2 ^ 9 ∧ M.accessible up (8 * ul) false = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧
  AW sp K up (8 * ul) ∧
  M.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧ Held R L mp (8 * n) ∧ AW sp K mp (8 * n) ∧
  NatNorm M up ul ∧ NatNorm M mp n ∧
  StkOK M R L st ∧ AW sp K st 24 ∧
  (0 < stCap M st → AW sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  stLen M st + 16 * ul + 64 ≤ 2 ^ 16 ∧ 0 < stCap M st ∧
  Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) ∧
  Apart mp (8 * n) st 24 ∧ Apart mp (8 * n) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) ∧
  (0 < qc → 0 < z2c → Apart qp (8 * qc) z2p (8 * z2c)) ∧
  (∀ p c, (p = qp ∧ c = qc) ∨ (p = z2p ∧ c = z2c) → 0 < c → Apart p (8 * c) up (8 * ul) ∧
    Apart p (8 * c) mp (8 * n) ∧ Apart p (8 * c) st 24 ∧
    Apart p (8 * c) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))) ∧
  costF (stLen M st) ul n ≤ cost ∧ cost ≤ b ∧ R.inv b L g (view R.rt L M)

/-- the callee's post about the remainder and the memory (memory form) -/
@[reducible] def DvPostG (R : RtInv) (b cost : Nat) (L L' : List (Nat × Nat)) (b' g sp stkD st qp qc z2p z2c up ul mp n : Nat)
    (M M' : Memory) (r rl rc : Nat) : Prop :=
  ExpHyp.NatOF R L L' M' z2p z2c 1 r rl rc (natVal M up ul % natVal M mp n) ∧
  LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧ StackBack R L L' st M M' ∧
  (¬ (r = z2p ∧ rc = z2c) → 0 < rc → 0 < stCap M' st → Apart r (8 * rc) (stW M' st) (8 * stCap M' st)) ∧
  MemFrame M M' (R.rt ++ [(sp - stkD, sp - 8), (sp + 8, sp + 112)] ++ [(qp, qp + 8 * qc), (z2p, z2p + 8 * z2c)] ++
    stkWs M st) ∧
  LiveFrame M M' L ([(qp, qp + 8 * qc), (z2p, z2p + 8 * z2c)] ++ stkWs M st) ∧ M'.regions = M.regions

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `nat.div` from its entry (return address `ra`, word `i` of window-4) to `ra` -/
theorem divCallG (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg34.name = false)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp K st qp ql qc z2p z2l z2c up ul uc mp n mc ra : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (hRA : RetAddr ((Extracted.program.onlySegments nsD).link impl) ra) (hra : ra < 2 ^ 64)
    (hpre : DvPreG R b costF costD L g sp K stkD st qp ql qc z2p z2l z2c up ul mp n M)
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hz2p : z2p < 2 ^ 64) (hup : up < 2 ^ 64) (huc : uc < 2 ^ 64)
    (hmp : mp < 2 ^ 64) (hmc : mc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h1 : S.regs 1 = BitVec.ofNat 64 ql)
    (h2 : S.regs 2 = BitVec.ofNat 64 qc) (h3 : S.regs 3 = BitVec.ofNat 64 st)
    (h4 : S.regs 4 = BitVec.ofNat 64 z2p) (h5 : S.regs 5 = BitVec.ofNat 64 z2l) (h6 : S.regs 6 = BitVec.ofNat 64 z2c)
    (h7 : S.regs 7 = BitVec.ofNat 64 up) (h8 : S.regs 8 = BitVec.ofNat 64 ul) (h9 : S.regs 9 = BitVec.ofNat 64 uc)
    (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h12 : S.regs 12 = BitVec.ofNat 64 mc) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KB : ∀ (S' : State) (M' : Memory) (L' : List (Nat × Nat)) (b' r rl rc : Nat),
      S'.pc = BitVec.ofNat 64 ra → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 r → S'.regs 4 = BitVec.ofNat 64 rl → S'.regs 5 = BitVec.ofNat 64 rc →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      DvPostG R b costD L L' b' g sp stkD st qp qc z2p z2c up ul mp n M M' r rl rc →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  obtain ⟨hce, hKD, hserv, hgl, hn128, hn, hqlc, hzlc, ⟨hqc, hqL, hqWG⟩, ⟨hzc, hzL, hzWG⟩, hul, hua, hu48, huH,
    huW, hma, hm48, hmH, hmW, huN, hmN, hsok, hstW, harr, hslen, hcap, huSt, huFr, hvSt, hvFr, hqz, hpair, hcF, hcost, hinv⟩ := hpre
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hS0 := LibWC.hypSum hap hnsD (hDiv b L (BitVec.ofNat 64 qp) (BitVec.ofNat 64 ql) (BitVec.ofNat 64 qc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 z2p) (BitVec.ofNat 64 z2l) (BitVec.ofNat 64 z2c) (BitVec.ofNat 64 up)
    (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) (BitVec.ofNat 64 mp) (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc))
  rw [show segAddr Extracted.program ExpHyp.fnDiv = divE by decide] at hS0
  have t0 := toNat_lt' hqp
  have t1 : (BitVec.ofNat 64 ql).toNat = ql := toNat_lt' (by omega)
  have t2 : (BitVec.ofNat 64 qc).toNat = qc := toNat_lt' (by omega)
  have t3 := toNat_lt' hst
  have t4 := toNat_lt' hz2p
  have t5 : (BitVec.ofNat 64 z2l).toNat = z2l := toNat_lt' (by omega)
  have t6 : (BitVec.ofNat 64 z2c).toNat = z2c := toNat_lt' (by omega)
  have t7 := toNat_lt' hup
  have t8 : (BitVec.ofNat 64 ul).toNat = ul := toNat_lt' (by omega)
  have t10 := toNat_lt' hmp
  have t11 : (BitVec.ofNat 64 n).toNat = n := toNat_lt' (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt' (by omega)
  have tg : (S.regs 28).toNat = g := by rw [h28]; exact toNat_lt' (by omega)
  refine Reaches.call_regions (hS0.withExit hret) hpc ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [h30, toNat_lt' hra]; exact hRA
  case args =>
    simp only [ArgsFrom]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, trivial⟩
  case pre =>
    simp only [ExpHyp.DivPre, ExpHyp.WrOut, ExpHyp.RdIn, ExpHyp.StackOK']
    rw [t0, t1, t2, t3, t4, t5, t6, t7, t8, t10, t11, hmem]
    have hce' := CallW.callEnv_of hce hsp h28 hmem (stk := stkD) (above := 112) hKD (by omega)
    simp only [win, tsp, tg]
    refine ⟨hce', hserv, globals_win hgl hKD, hqlc, hzlc,
      ⟨hqc, hqL, fun h => ⟨out_win hKD (hqWG h).1, (hqWG h).2⟩⟩, ⟨hzc, hzL, fun h => ⟨out_win hKD (hzWG h).1, (hzWG h).2⟩⟩,
      ⟨by omega, hua, hu48, huH, out_win hKD huW⟩, ⟨by omega, hma, hm48, hmH, out_win hKD hmW⟩, hul, hn, by omega,
      huN, hmN, hsok, out_win hKD hstW, fun hc => ⟨out_win hKD (harr hc).1, (harr hc).2⟩, hslen,
      fun h => absurd h (by omega), huSt, huFr, hvSt, hvFr,
      hqz, fun p c hpc' hc0 => ?_, Nat.le_trans hcF hcost, hinv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpc'
    exact hpair p c hpc' hc0
  obtain ⟨q, ql', qc', r, rl, rc, hX0, hX1, hX2, hX3, hX4, hX5, L', b', hqOF, hrOF, ⟨hLE, hb', hinv'⟩, hsb, hfr, hF, hLF⟩ :=
    hq
  simp only [t0, t1, t2, t3, t4, t5, t6, t7, t8, t10, t11, hmem, tsp, tg, winA] at hqOF hrOF hb' hinv' hsb hfr hF hLF
  refine KB s' s'.mem L' b' r rl rc (hr.trans h30) (e1.trans hsp) hX3 hX4 hX5 (e4.trans h18) (e2.trans h28)
    (e3.trans h29) rfl ⟨hrOF, hLE, by omega, hinv', hsb, hfr, hF, hLF, by rw [hrg, hmem]⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a `div` call whose written nats lie in the stack above `l0` keeps the context without `x` -/
theorem keeps_divB {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret b b' costD stkD qp qc z2p z2c up ul r rl rc : Nat}
    {r29 : BitVec 64} {ex : List (Nat × Nat)} {M M' : Memory}
    (hC : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) (hKD : stkD ≤ K)
    (hqx : (qp, 8 * qc) ∈ ex) (hqa : M.accessible qp (8 * qc) true = true) (hqW : AW sp K qp (8 * qc))
    (hqG : Apart qp (8 * qc) (g + 16) 8)
    (hzin : stW M st + 8 * l0 ≤ z2p ∧ z2p + 8 * z2c ≤ stW M st + 8 * stLen M st)
    (hlpos : 0 < stLen M st)
    (hD : DvPostG R b costD L L' b' g sp stkD st qp qc z2p z2c up ul mp n M M' r rl rc) :
    KeepsB R L L' g sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hfe, -, hstw, hsok, -, hl0, hcap, -, hug, huw, hsu, -, -, -, -, -,
    -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨-, hxD, -, -, ⟨hsok', hlen', hst'⟩, -, hF, hL, hrg⟩ := hD
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro'⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  have hstg := hfe.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hfe hLs hd hro'
  simp only [AW, Apart, stUp] at hstw huw hug hsu hga hstg hqW hqG
  refine keeps_ofB hce hK hxD (by simpa only [List.append_assoc] using hF) hL hrg ?_ ?_ ?_ ?_ ?_ ?_ hsok'
    (by omega) hst' ?_
  · clear hstw huw hug hsu hga hstg hqW hqG
    intro r' hr' hlt
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simp only at hlt ⊢; exact M.accessible_sub hqa (Or.inr rfl) (by omega) (by omega)
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hsu
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug hsu hga hstg hqW hqG
    intro a k' ho
    obtain ⟨-, o2, o3, o4, o5⟩ := ho
    have o6 := o5 _ hqx
    clear o5
    simp only [AW, Apart, stUp] at o2 o3 o4 o6
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  · clear hug hsu hga hstg
    intro j hj
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hug hsu hga hstg
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hug hsu hga hstg
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug hsu hga hstg
    intro _
    have := hsok'.2.2.2.2.2.1
    simp only [stLen, stCap] at hlen' this hlpos ⊢; omega

end FvModexp.Arm64.W4Pro
