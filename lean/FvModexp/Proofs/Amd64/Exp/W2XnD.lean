import FvModexp.Proofs.Amd64.Exp.W2Div
import FvModexp.Proofs.Amd64.Exp.W2XnK

set_option autoImplicit false

/-!
# window-2 prologue (amd64): a general `nat.div` call `q, r = z.div(stk, z2, u, m)` (`divCallG`)
(agent expmc s55; twin of `Arm64.W2XnD`)

Generalisation of `divCall` (W2Div) to any `z = (qp, ql, qc)`, `z2 = (z2p, z2l, z2c)`, `u = (up, ul, uc)` and any
return address `fn + i` at `[sp - 8]`; used by the `x` normalisation (nat.go:1378, `x mod m`, return `aDivRet`).
`keeps_divX`: such a call (`q` an extra range of the context, `z2` in the stack above the context's level) keeps
`CtxX`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W2Pro

/-- a written argument nat of the `div` call (memory form) -/
@[reducible] def DvOut (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (M : Memory) (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L p c ∧ (0 < c → AWx sp K p (8 * c) ∧ Apart p (8 * c) (g + 16) 8 ∧
    Apart p (8 * c) (fs - 8) 8 ∧ Apart p (8 * c) RunIface.gA 32)

/-- the facts at a general `div` call (memory form; `sp` = window-2's `RSP`) -/
@[reducible] def DvPreG (R : RtInv) (b : Nat) (costF : Nat → Nat → Nat → Nat) (cost : Nat) (L : List (Nat × Nat))
    (g fs sp K stkD st qp ql qc z2p z2l z2c up ul uc mp n mc : Nat) (M : Memory) : Prop :=
  CallW.CEnv R L g fs (sp - 8) K 688 M ∧ stkD ≤ K ∧ RunIface.Serves R ∧
  RunIface.Globals R M [(sp - 8 - stkD, sp - 8 + 112)] ∧ n ≤ 128 ∧ 0 < n ∧
  M.readLE sp 8 = up ∧ M.readLE (sp + 8) 8 = ul ∧ M.readLE (sp + 16) 8 = uc ∧ M.readLE (sp + 24) 8 = mp ∧
  M.readLE (sp + 32) 8 = n ∧ M.readLE (sp + 40) 8 = mc ∧
  ql ≤ qc ∧ z2l ≤ z2c ∧ DvOut R L g fs sp K M qp qc ∧ DvOut R L g fs sp K M z2p z2c ∧
  ul ≤ 2 ^ 9 ∧ M.accessible up (8 * ul) false = true ∧ up + 8 * ul ≤ 2 ^ 48 ∧ Held R L up (8 * ul) ∧
  AWx sp K up (8 * ul) ∧
  M.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧ Held R L mp (8 * n) ∧ AWx sp K mp (8 * n) ∧
  NatNorm M up ul ∧ NatNorm M mp n ∧
  StkOK M R L st ∧ AWx sp K st 24 ∧
  (0 < stCap M st → AWx sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  stLen M st + 16 * ul + 64 ≤ 2 ^ 16 ∧ 0 < stCap M st ∧
  Apart up (8 * ul) st 24 ∧ Apart up (8 * ul) (stFree M st).1 (stFree M st).2 ∧
  Apart mp (8 * n) st 24 ∧ Apart mp (8 * n) (stFree M st).1 (stFree M st).2 ∧
  (0 < qc → 0 < z2c → Apart qp (8 * qc) z2p (8 * z2c)) ∧
  (∀ p c, (p = qp ∧ c = qc) ∨ (p = z2p ∧ c = z2c) → 0 < c → Apart p (8 * c) up (8 * ul) ∧
    Apart p (8 * c) mp (8 * n) ∧ Apart p (8 * c) st 24 ∧ Apart p (8 * c) (stFree M st).1 (stFree M st).2) ∧
  st ≠ 0 ∧ Apart st 24 RunIface.gA 32 ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (stFree M st).1 (stFree M st).2 ∧ Apart st 24 (fs - 8) 8 ∧ Apart (stFree M st).1 (stFree M st).2 (fs - 8) 8 ∧
  Apart (stFree M st).1 (stFree M st).2 RunIface.gA 32 ∧
  costF (stLen M st) ul n ≤ cost ∧ cost ≤ b ∧ R.inv b L g (view R.rt L M)

/-- the callee's post about the remainder and the memory (memory form) -/
@[reducible] def DvPostG (R : RtInv) (b cost : Nat) (L L' : List (Nat × Nat))
    (b' g sp stkD st qp qc z2p z2c up ul mp n : Nat) (M M' : Memory) (r rl rc : Nat) : Prop :=
  ExpHyp.NatOF R L L' M' z2p z2c 1 r rl rc (natVal M up ul % natVal M mp n) ∧
  LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧ StackBackL R L L' st M M' ∧
  (¬ (r = z2p ∧ rc = z2c) → 0 < rc → 0 < stCap M' st → Apart r (8 * rc) (stW M' st) (8 * stCap M' st)) ∧
  MemFrame M M' (R.rt ++ [(sp - 8 - stkD, sp - 8 + 112)] ++ [(qp, qp + 8 * qc), (z2p, z2p + 8 * z2c)] ++
    stkWs M st) ∧
  LiveFrame M M' L ([(qp, qp + 8 * qc), (z2p, z2p + 8 * z2c)] ++ stkWs M st) ∧ M'.regions = M.regions

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `DvPreG` at the call state gives `nat.div`'s precondition -/
theorem dvg_pre {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {cost : Nat} {L : List (Nat × Nat)}
    {g fs sp K stkD st qp ql qc z2p z2l z2c up ul uc mp n mc : Nat} {S : State}
    (hpre : DvPreG R b costF cost L g fs sp K stkD st qp ql qc z2p z2l z2c up ul uc mp n mc S.mem)
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hz2p : z2p < 2 ^ 64)
    (tsp : (S.regs 4).toNat = sp - 8) (tg : (S.regs 14).toNat = g) (hfs : S.fsBase.toNat = fs)
    (hadx : S.mem.accessible Callees.adxAddr 1 false = true) :
    ExpHyp.DivPre R b costF L stkD 112 (BitVec.ofNat 64 qp).toNat (BitVec.ofNat 64 ql).toNat
      (BitVec.ofNat 64 qc).toNat (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 z2p).toNat (BitVec.ofNat 64 z2l).toNat
      (BitVec.ofNat 64 z2c).toNat up ul uc mp n mc S := by
  obtain ⟨hce, hKD, hserv, hgl, hn128, hn, a0, a1, a2, a3, a4, a5, hqlc, hzlc, ⟨hqc, hqL, hqWG⟩, ⟨hzc, hzL, hzWG⟩,
    hul, hua, hu48, huH, huW, hma, hm48, hmH, hmW, huN, hmN, hsok, hstW, harr, hslen, hcap, huSt, huFr, hvSt, hvFr,
    hqz, hpair, hstz, hgst, hstg, hstwb, hstf, hstfs, hffs, hgfr, hcF, hcost, hinv⟩ := hpre
  have hK : K ≤ sp - 8 := hce.2.1
  have t0 := MontW.toNat_of hqp
  have t1 : (BitVec.ofNat 64 ql).toNat = ql := MontW.toNat_of (by omega)
  have t2 : (BitVec.ofNat 64 qc).toNat = qc := MontW.toNat_of (by omega)
  have t3 := MontW.toNat_of hst
  have t4 := MontW.toNat_of hz2p
  have t5 : (BitVec.ofNat 64 z2l).toNat = z2l := MontW.toNat_of (by omega)
  have t6 : (BitVec.ofNat 64 z2c).toNat = z2c := MontW.toNat_of (by omega)
  simp only [ExpHyp.DivPre, EvenHyp.WrOut, EvenHyp.RdIn, ExpHyp.StackOK']
  rw [t0, t1, t2, t3, t4, t5, t6, tsp, show sp - 8 + 8 = sp by omega, show sp - 8 + 16 = sp + 8 by omega,
    show sp - 8 + 24 = sp + 16 by omega, show sp - 8 + 32 = sp + 24 by omega, show sp - 8 + 40 = sp + 32 by omega,
    show sp - 8 + 48 = sp + 40 by omega]
  have hce' := CallW.callEnv_of hce tsp tg hfs rfl (stk := stkD) (above := 112) hKD (by omega) (by omega)
  simp only [win, tsp, tg, hfs]
  refine ⟨a0, a1, a2, a3, a4, a5, hce', hserv, hgl, hqlc, hzlc,
    ⟨hqc, hqL, fun h => ⟨out_winx hKD (hqWG h).1, (hqWG h).2.1, (hqWG h).2.2.1⟩⟩,
    ⟨hzc, hzL, fun h => ⟨out_winx hKD (hzWG h).1, (hzWG h).2.1, (hzWG h).2.2.1⟩⟩,
    ⟨by omega, hua, hu48, huH, out_winx hKD huW⟩, ⟨by omega, hma, hm48, hmH, out_winx hKD hmW⟩, hul, hn, by omega,
    huN, hmN, hsok, out_winx hKD hstW, fun hc => ⟨out_winx hKD (harr hc).1, (harr hc).2⟩, hslen,
    fun h => absurd h (by omega), huSt, huFr, hvSt, hvFr, hstz, ⟨hstg, hstwb, hstf⟩, ⟨hstfs, hffs⟩,
    fun h => (hqWG h).2.2.2, fun h => (hzWG h).2.2.2, hgst, hgfr, hqz, fun p c hpc' hc0 => ?_,
    Nat.le_trans hcF hcost, hadx, hinv⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpc'
  exact hpair p c hpc' hc0

/-- `nat.div`'s post at the return state gives `DvPostG` -/
theorem dvg_post {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {cost : Nat} {L : List (Nat × Nat)}
    {g sp stkD st qp qc z2p z2c up ul mp n : Nat} {S s' : State}
    (hq : ExpHyp.DivPostL R b costF L stkD 112 (BitVec.ofNat 64 qp).toNat (BitVec.ofNat 64 qc).toNat
      (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 z2p).toNat (BitVec.ofNat 64 z2c).toNat up ul mp n S s')
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hz2p : z2p < 2 ^ 64) (hqc : qc < 2 ^ 64) (hz2c : z2c < 2 ^ 64)
    (tsp : (S.regs 4).toNat = sp - 8) (tg : (S.regs 14).toNat = g) (hcF : costF (stLen S.mem st) ul n ≤ cost)
    (hrg : s'.mem.regions = S.mem.regions) :
    s'.fsBase = S.fsBase ∧ s'.df = S.df ∧ ∃ (L' : List (Nat × Nat)) (b' r rl rc : Nat),
      s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧ s'.regs 8 = BitVec.ofNat 64 rc ∧
      DvPostG R b cost L L' b' g sp stkD st qp qc z2p z2c up ul mp n S.mem s'.mem r rl rc := by
  obtain ⟨efs, edf, q, ql, qc', r, rl, rc, hX0, hX1, hX2, hX3, hX4, hX5, L', b', hqOF, hrOF, ⟨hLE, hb', hinv'⟩, hsb,
    hfr, hF, hLF⟩ := hq
  have t0 := MontW.toNat_of hqp
  have t2 := MontW.toNat_of hqc
  have t3 := MontW.toNat_of hst
  have t4 := MontW.toNat_of hz2p
  have t6 := MontW.toNat_of hz2c
  simp only [t0, t2, t3, t4, t6] at hF hLF hfr hsb hrOF hb'
  rw [tg] at hinv'
  simp only [win, tsp] at hF
  exact ⟨efs, edf, L', b', r, rl, rc, hX3, hX4, hX5, hrOF, hLE, by omega, hinv', hsb, hfr, hF, hLF, hrg⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.div` from its entry (return address `fn + i` at `[sp - 8]`) to `fn + i` -/
theorem divCallG {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W2Loop.fn = false)
    (i : Nat) (hi : i < 0x1280)
    {ret : W64} {Q : State → Prop} {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K st qp ql qc z2p z2l z2c up ul uc mp n mc : Nat} {r5 : W64}
    (S : State) (hpre : DvPreG R b costF costD L g fs sp K stkD st qp ql qc z2p z2l z2c up ul uc mp n mc S.mem)
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hz2p : z2p < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 divE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hrd : S.mem.readLE (sp - 8) 8 = 6210560 + i)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h3 : S.regs 3 = BitVec.ofNat 64 ql)
    (h1 : S.regs 1 = BitVec.ofNat 64 qc) (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (h6 : S.regs 6 = BitVec.ofNat 64 z2p) (h8 : S.regs 8 = BitVec.ofNat 64 z2l) (h9 : S.regs 9 = BitVec.ofNat 64 z2c)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) (hadx : S.mem.accessible Callees.adxAddr 1 false = true)
    (KB : ∀ (S' : State) (L' : List (Nat × Nat)) (b' r rl rc : Nat),
      S'.rip = BitVec.ofNat 64 (6210560 + i) → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 r → S'.regs 6 = BitVec.ofNat 64 rl → S'.regs 8 = BitVec.ofNat 64 rc →
      DvPostG R b costD L L' b' g sp stkD st qp qc z2p z2c up ul mp n S.mem S'.mem r rl rc →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hpre0 := hpre
  obtain ⟨hce, hKD, -, -, hn128, -, -, -, -, -, -, -, hqlc, hzlc, ⟨hqc, -⟩, ⟨hzc, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcF, -⟩ := hpre0
  have hK : K ≤ sp - 8 := hce.2.1
  have hs8 : 8 ≤ sp := by omega
  have hs64 : sp < 2 ^ 64 := by omega
  have hce0 := hce
  obtain ⟨-, -, hA, -, hg1, -, hg3, -⟩ := hce0
  have hc : CodeIn64 ((Extracted.program.onlySegments nsD).link impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact A64.codeIn_restrict_mono64 hap hnsD
  have hS := Ensures.toSummaryIn (hDiv b L (BitVec.ofNat 64 qp) (BitVec.ofNat 64 ql) (BitVec.ofNat 64 qc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 z2p) (BitVec.ofNat 64 z2l) (BitVec.ofNat 64 z2c) up ul uc mp n mc)
    (A64.noExit_restrict64 hap nsD) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide) hc
  rw [divE_eq] at hS
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tg : (S.regs 14).toNat = g := by rw [h14]; exact MontW.toNat_of (by omega)
  have t0 := MontW.toNat_of hqp
  have t1 : (BitVec.ofNat 64 ql).toNat = ql := MontW.toNat_of (by omega)
  have t2 : (BitVec.ofNat 64 qc).toNat = qc := MontW.toNat_of (by omega)
  have t3 := MontW.toNat_of hst
  have t4 := MontW.toNat_of hz2p
  have t5 : (BitVec.ofNat 64 z2l).toNat = z2l := MontW.toNat_of (by omega)
  have t6 : (BitVec.ofNat 64 z2c).toNat = z2c := MontW.toNat_of (by omega)
  refine ReachesRet.call_regions hS hpc ⟨?ra, hx15, ?args, hdf, ?pre⟩ (fun s' hr ⟨⟨e4, e5, e14, ex15⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [tsp, hrd]; exact W2Loop.ra_of hap hnsW i hi
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨h0, h3, h1, h7, h6, h8, h9, trivial⟩
  case pre => exact dvg_pre hpre hst hqp hz2p tsp tg hfs hadx
  obtain ⟨efs, edf, L', b', r, rl, rc, hX3, hX4, hX5, hpost⟩ :=
    dvg_post hq hst hqp hz2p (by omega) (by omega) tsp tg hcF hrg
  exact KB s' L' b' r rl rc (by rw [hr, retAddrOf_eq, tsp, hrd])
    (by rw [e4, hsp]; exact W2Loop.sp_add8 hs8 hs64) (e5.trans h5) (e14.trans h14) (by rw [efs, hfs])
    (by rw [ex15, hx15]) (by rw [edf, hdf]) hX3 hX4 hX5 hpost

end FvModexp.Amd64.W2Pro
