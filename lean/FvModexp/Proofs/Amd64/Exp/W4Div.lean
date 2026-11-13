import FvModexp.Proofs.Amd64.Exp.W4RR
import FvModexp.Proofs.Amd64.Exp.ExpHyp
import FvModexp.Proofs.Amd64.Exp.W4Snc

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the call `_, RR = nat(stk.nat(2n)).div(stk, RR, zz, m)` (nat.go:1399), `divE → divRet`
(agent expmc s51; twin of `Arm64.W4Div`)

`nat.div` is a premise in expmc's `ExpHyp.DivHypL` shape (asm proves it: `ExpHyp.DivHypL impl R names 41512 112 _`),
parametric in its names `nsD`, its stack bound `stkD ≤ K` and its closed cost `costD`. The caller's window is
`CallW.CEnv … (sp - 8) K 968` (`sp` = window-4's `RSP`; `K` = the deepest callee window). Arguments: `z` = the fresh
stack nat `q` (AX/BX/CX, `2n` words), `stk` (DI), `z2` = `RR` (SI/R8/R9: pointer, len 1, cap `2n`), and on the stack
(`[sp, sp + 48)`) `u` = `zz` (`2^(128n)`), `v` = `m`. Return address `divRet` = fn+0x5e5.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Pro

/-- entry of `nat.div` -/
abbrev divE : Nat := 6217504

theorem divE_eq : segAddr Extracted.program ExpHyp.fnDiv = divE := by decide

/-- apart from window-4's frame with the deepest callee window `K` (caller window `[sp - 8 - K, sp + 0x3c0)`) -/
@[reducible] def AWx (sp K a k : Nat) : Prop := Apart a k (sp - 8 - K) (K + 968)

/-- the facts at the `div` call (memory form; `sp` = window-4's `RSP`) -/
@[reducible] def DvPre (R : RtInv) (b : Nat) (costF : Nat → Nat → Nat → Nat) (cost : Nat) (L : List (Nat × Nat))
    (g fs sp K stkD st qp rrp n zzp zzl zzc mp mc : Nat) (M : Memory) : Prop :=
  CallW.CEnv R L g fs (sp - 8) K 968 M ∧ stkD ≤ K ∧ RunIface.Serves R ∧
  RunIface.Globals R M [(sp - 8 - stkD, sp - 8 + 112)] ∧ n ≤ 128 ∧ 0 < n ∧
  M.readLE sp 8 = zzp ∧ M.readLE (sp + 8) 8 = zzl ∧ M.readLE (sp + 16) 8 = zzc ∧ M.readLE (sp + 24) 8 = mp ∧
  M.readLE (sp + 32) 8 = n ∧ M.readLE (sp + 40) 8 = mc ∧
  NatLive M R L qp (2 * n) ∧ AWx sp K qp (8 * (2 * n)) ∧ Apart qp (8 * (2 * n)) (g + 16) 8 ∧
  Apart qp (8 * (2 * n)) (fs - 8) 8 ∧
  NatLive M R L rrp (2 * n) ∧ AWx sp K rrp (8 * (2 * n)) ∧ Apart rrp (8 * (2 * n)) (g + 16) 8 ∧
  Apart rrp (8 * (2 * n)) (fs - 8) 8 ∧
  zzl ≤ 2 ^ 9 ∧ M.accessible zzp (8 * zzl) false = true ∧ zzp + 8 * zzl ≤ 2 ^ 48 ∧ Held R L zzp (8 * zzl) ∧
  AWx sp K zzp (8 * zzl) ∧
  M.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧ Held R L mp (8 * n) ∧ AWx sp K mp (8 * n) ∧
  NatNorm M zzp zzl ∧ NatNorm M mp n ∧
  StkOK M R L st ∧ AWx sp K st 24 ∧
  (0 < stCap M st → AWx sp K (stW M st) (8 * stCap M st) ∧ Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  stLen M st + 16 * zzl + 64 ≤ 2 ^ 16 ∧ 0 < stCap M st ∧
  Apart zzp (8 * zzl) st 24 ∧ Apart zzp (8 * zzl) (stFree M st).1 (stFree M st).2 ∧
  Apart mp (8 * n) st 24 ∧ Apart mp (8 * n) (stFree M st).1 (stFree M st).2 ∧
  Apart qp (8 * (2 * n)) rrp (8 * (2 * n)) ∧
  (∀ p, p = qp ∨ p = rrp → Apart p (8 * (2 * n)) zzp (8 * zzl) ∧ Apart p (8 * (2 * n)) mp (8 * n) ∧
    Apart p (8 * (2 * n)) st 24 ∧ Apart p (8 * (2 * n)) (stFree M st).1 (stFree M st).2) ∧
  Apart qp (8 * (2 * n)) RunIface.gA 32 ∧ Apart rrp (8 * (2 * n)) RunIface.gA 32 ∧
  st ≠ 0 ∧ Apart st 24 RunIface.gA 32 ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (stFree M st).1 (stFree M st).2 ∧ Apart st 24 (fs - 8) 8 ∧ Apart (stFree M st).1 (stFree M st).2 (fs - 8) 8 ∧
  Apart (stFree M st).1 (stFree M st).2 RunIface.gA 32 ∧
  costF (stLen M st) zzl n ≤ cost ∧ cost ≤ b ∧ R.inv b L g (view R.rt L M)

/-- the callee's post about the remainder and the memory (memory form) -/
@[reducible] def DvPost (R : RtInv) (b cost : Nat) (L L' : List (Nat × Nat)) (b' g sp stkD st qp rrp n zzp zzl mp : Nat)
    (M M' : Memory) (r rl rc : Nat) : Prop :=
  ExpHyp.NatOF R L L' M' rrp (2 * n) 1 r rl rc (natVal M zzp zzl % natVal M mp n) ∧
  LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧ StackBackL R L L' st M M' ∧
  (¬ (r = rrp ∧ rc = 2 * n) → 0 < rc → 0 < stCap M' st → Apart r (8 * rc) (stW M' st) (8 * stCap M' st)) ∧
  MemFrame M M' (R.rt ++ [(sp - 8 - stkD, sp - 8 + 112)] ++ [(qp, qp + 8 * (2 * n)), (rrp, rrp + 8 * (2 * n))] ++
    stkWs M st) ∧
  LiveFrame M M' L ([(qp, qp + 8 * (2 * n)), (rrp, rrp + 8 * (2 * n))] ++ stkWs M st) ∧ M'.regions = M.regions

theorem out_winx {sp K stkD a k : Nat} (hKD : stkD ≤ K) (h : AWx sp K a k) :
    Outside a k [(sp - 8 - stkD, sp - 8 + 112)] := by
  simp only [AWx, Apart] at h; simp only [outside_cons, outside_nil, and_true]; omega

/-- the scalar facts `divCall` needs besides the pre -/
theorem dv_facts {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {cost : Nat} {L : List (Nat × Nat)}
    {g fs sp K stkD st qp rrp n zzp zzl zzc mp mc : Nat} {M : Memory}
    (hpre : DvPre R b costF cost L g fs sp K stkD st qp rrp n zzp zzl zzc mp mc M) :
    n ≤ 128 ∧ K ≤ sp - 8 ∧ costF (stLen M st) zzl n ≤ cost ∧ 8 ≤ sp ∧ sp < 2 ^ 64 ∧ g < 2 ^ 64 := by
  obtain ⟨hce, hKD, hserv, hgl, hn128, hn, a0, a1, a2, a3, a4, a5, hqL, hqW, hqG, hqF, hrL, hrW, hrG, hrF, hzl, hza,
    hz48, hzH, hzW, hma, hm48, hmH, hmW, hzN, hmN, hsok, hstW, harr, hslen, hcap, huH, huF, hvH, hvF, hqr, hpair, hgq,
    hgz, hstz, hgst, hstg, hstwb, hstf, hstfs, hffs, hgfr, hcF, hcost, hinv⟩ := hpre
  have hK := hce.2.1
  obtain ⟨-, -, hA, -, hg1, -, hg3, -⟩ := hce
  exact ⟨hn128, hK, hcF, by omega, by omega, by omega⟩

/-- `DvPre` at the call state gives `nat.div`'s precondition -/
theorem dv_pre {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {cost : Nat} {L : List (Nat × Nat)}
    {g fs sp K stkD st qp rrp n zzp zzl zzc mp mc : Nat} {S : State}
    (hpre : DvPre R b costF cost L g fs sp K stkD st qp rrp n zzp zzl zzc mp mc S.mem)
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hrrp : rrp < 2 ^ 64)
    (tsp : (S.regs 4).toNat = sp - 8) (tg : (S.regs 14).toNat = g) (hfs : S.fsBase.toNat = fs) :
    ExpHyp.DivPre R b costF L stkD 112 (BitVec.ofNat 64 qp).toNat (BitVec.ofNat 64 (2 * n)).toNat
      (BitVec.ofNat 64 (2 * n)).toNat (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 rrp).toNat (BitVec.ofNat 64 1).toNat
      (BitVec.ofNat 64 (2 * n)).toNat zzp zzl zzc mp n mc S := by
  obtain ⟨hce, hKD, hserv, hgl, hn128, hn, a0, a1, a2, a3, a4, a5, hqL, hqW, hqG, hqF, hrL, hrW, hrG, hrF, hzl, hza,
    hz48, hzH, hzW, hma, hm48, hmH, hmW, hzN, hmN, hsok, hstW, harr, hslen, hcap, huH, huF, hvH, hvF, hqr, hpair, hgq,
    hgz, hstz, hgst, hstg, hstwb, hstf, hstfs, hffs, hgfr, hcF, hcost, hinv⟩ := hpre
  have hK : K ≤ sp - 8 := hce.2.1
  have t0 := MontW.toNat_of hqp
  have t1 : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := MontW.toNat_of (by omega)
  have t3 := MontW.toNat_of hst
  have t4 := MontW.toNat_of hrrp
  have t5 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  simp only [ExpHyp.DivPre, EvenHyp.WrOut, EvenHyp.RdIn, ExpHyp.StackOK']
  have hK : K ≤ sp - 8 := hce.2.1
  rw [t0, t1, t3, t4, t5, tsp, show sp - 8 + 8 = sp by omega, show sp - 8 + 16 = sp + 8 by omega,
    show sp - 8 + 24 = sp + 16 by omega, show sp - 8 + 32 = sp + 24 by omega, show sp - 8 + 40 = sp + 32 by omega,
    show sp - 8 + 48 = sp + 40 by omega]
  have hce' := CallW.callEnv_of hce tsp tg hfs rfl (stk := stkD) (above := 112) hKD (by omega) (by omega)
  simp only [win, tsp, tg, hfs]
  refine ⟨a0, a1, a2, a3, a4, a5, hce', hserv, hgl, Nat.le_refl _, by omega,
    ⟨by omega, hqL, fun _ => ⟨out_winx hKD hqW, hqG, hqF⟩⟩, ⟨by omega, hrL, fun _ => ⟨out_winx hKD hrW, hrG, hrF⟩⟩,
    ⟨by omega, hza, hz48, hzH, out_winx hKD hzW⟩, ⟨by omega, hma, hm48, hmH, out_winx hKD hmW⟩, hzl, hn, by omega,
    hzN, hmN, hsok, out_winx hKD hstW, fun hc => ⟨out_winx hKD (harr hc).1, (harr hc).2⟩, hslen,
    fun h => absurd h (by omega), huH, huF, hvH, hvF, hstz, ⟨hstg, hstwb, hstf⟩, ⟨hstfs, hffs⟩,
    fun _ => hgq, fun _ => hgz, hgst, hgfr, fun _ _ => hqr, fun p c hpc' _ => ?_, Nat.le_trans hcF hcost, hinv⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpc'
  rcases hpc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hpair _ (Or.inl rfl)
  · exact hpair _ (Or.inr rfl)

/-- `nat.div`'s post at the return state gives `DvPost` -/
theorem dv_post {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {cost : Nat} {L : List (Nat × Nat)}
    {g sp stkD st qp rrp n zzp zzl mp : Nat} {S s' : State}
    (hq : ExpHyp.DivPostL R b costF L stkD 112 (BitVec.ofNat 64 qp).toNat (BitVec.ofNat 64 (2 * n)).toNat
      (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 rrp).toNat (BitVec.ofNat 64 (2 * n)).toNat zzp zzl mp n S s')
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hrrp : rrp < 2 ^ 64) (hn : n ≤ 128)
    (tsp : (S.regs 4).toNat = sp - 8) (tg : (S.regs 14).toNat = g) (hcF : costF (stLen S.mem st) zzl n ≤ cost)
    (hrg : s'.mem.regions = S.mem.regions) :
    s'.fsBase = S.fsBase ∧ s'.df = S.df ∧ ∃ (L' : List (Nat × Nat)) (b' r rl rc : Nat),
      s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧ s'.regs 8 = BitVec.ofNat 64 rc ∧
      DvPost R b cost L L' b' g sp stkD st qp rrp n zzp zzl mp S.mem s'.mem r rl rc := by
  obtain ⟨efs, edf, q, ql, qc, r, rl, rc, hX0, hX1, hX2, hX3, hX4, hX5, L', b', hqOF, hrOF, ⟨hLE, hb', hinv'⟩, hsb,
    hfr, hF, hLF⟩ := hq
  have t0 := MontW.toNat_of hqp
  have t1 : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := MontW.toNat_of (by omega)
  have t3 := MontW.toNat_of hst
  have t4 := MontW.toNat_of hrrp
  simp only [t0, t1, t3, t4] at hF hLF hfr hsb hrOF hb'
  rw [tg] at hinv'
  simp only [win, tsp] at hF
  exact ⟨efs, edf, L', b', r, rl, rc, hX3, hX4, hX5, hrOF, hLE, by omega, hinv', hsb, hfr, hF, hLF, hrg⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.div` from its entry (return address `divRet` at `[sp - 8]`) to `divRet` -/
theorem divCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W4Loop.fn = false)
    {ret : W64} {Q : State → Prop} {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K st qp rrp n zzp zzl zzc mp mc : Nat} {r5 : W64}
    (S : State) (hpre : DvPre R b costF costD L g fs sp K stkD st qp rrp n zzp zzl zzc mp mc S.mem)
    (hst : st < 2 ^ 64) (hqp : qp < 2 ^ 64) (hrrp : rrp < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 divE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hrd : S.mem.readLE (sp - 8) 8 = divRet)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h3 : S.regs 3 = BitVec.ofNat 64 (2 * n))
    (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n)) (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (h6 : S.regs 6 = BitVec.ofNat 64 rrp) (h8 : S.regs 8 = BitVec.ofNat 64 1) (h9 : S.regs 9 = BitVec.ofNat 64 (2 * n))
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KB : ∀ (S' : State) (L' : List (Nat × Nat)) (b' r rl rc : Nat),
      S'.rip = BitVec.ofNat 64 divRet → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 r → S'.regs 6 = BitVec.ofNat 64 rl → S'.regs 8 = BitVec.ofNat 64 rc →
      DvPost R b costD L L' b' g sp stkD st qp rrp n zzp zzl mp S.mem S'.mem r rl rc →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  obtain ⟨hn, hK, hcF, hs8, hs64, hg64⟩ := dv_facts hpre
  have hc : CodeIn64 ((Extracted.program.onlySegments nsD).link impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact A64.codeIn_restrict_mono64 hap hnsD
  have hS := Ensures.toSummaryIn (hDiv b L (BitVec.ofNat 64 qp) (BitVec.ofNat 64 (2 * n)) (BitVec.ofNat 64 (2 * n))
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 rrp) (BitVec.ofNat 64 1) (BitVec.ofNat 64 (2 * n)) zzp zzl zzc mp n mc)
    (A64.noExit_restrict64 hap nsD) (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide) hc
  rw [divE_eq] at hS
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tg : (S.regs 14).toNat = g := by rw [h14]; exact MontW.toNat_of (by omega)
  refine ReachesRet.call_regions hS hpc ⟨?ra, hx15, ?args, hdf, dv_pre hpre hst hqp hrrp tsp tg hfs⟩
    (fun s' hr ⟨⟨e4, e5, e14, ex15⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [tsp, hrd]; exact W4Loop.ra_of hap hnsW 0x5e5 (by decide)
  case args =>
    simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨h0, h3, h1, h7, h6, h8, h9, trivial⟩
  obtain ⟨efs, edf, L', b', r, rl, rc, hX3, hX4, hX5, hpost⟩ := dv_post hq hst hqp hrrp hn tsp tg hcF hrg
  exact KB s' L' b' r rl rc (by rw [hr, retAddrOf_eq, tsp, hrd])
    (by rw [e4, hsp]; exact W4Loop.sp_add8 hs8 hs64) (e5.trans h5) (e14.trans h14) (by rw [efs, hfs])
    (by rw [ex15, hx15]) (by rw [edf, hdf]) hX3 hX4 hX5 hpost

end FvModexp.Amd64.W4Pro
