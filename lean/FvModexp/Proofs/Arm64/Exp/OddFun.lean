import FvModexp.Proofs.Arm64.Exp.OddPro
import FvModexp.Proofs.Arm64.Exp.OddPost
import FvModexp.Proofs.Arm64.Exp.W4FunE
import FvModexp.Proofs.Arm64.Exp.W2FunE

/-!
# `nat.expNNOdd` (arm64): `ens` / `sum` (CONVENTIONS §3)

`z.expNNOdd(stk, x, y, m)` returns `x^y mod m` (see `Pre`/`Post`): the prologue (`pro`), the call of window-4
(`ExpW4.ens`, `len y > 1`) or window-2 (`ExpW2.ens`), the epilogue (`epi`). Premises: the live runtime contracts and
`nat.div`'s shape `ExpHyp.DivHyp` (as the windows).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpOdd

/-- an `Ensures` on `(Extracted.program.onlySegments ns).link impl` (`ns ⊆ LibOdd.names`) as a `Summary` of
`LibOdd.program.link impl` -/
theorem hypSumO {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibOdd.names.contains x = true) {f : String} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibOdd.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibOdd.eq_only] at hS
  exact hS

set_option maxHeartbeats 64000000 in
theorem w_sub : ∀ x, LibW.names.contains x = true → LibOdd.names.contains x = true := MontW.sub_of_all (by decide)

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ra4 (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments LibW.names).link impl) 1798404 :=
  CallW.retAddr_restrict hap (cs := Extracted.seg21)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 13
    (by decide) (by decide) (by decide)

theorem ra2 (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments LibW.names).link impl) 1798420 :=
  CallW.retAddr_restrict hap (cs := Extracted.seg21)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 17
    (by decide) (by decide) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNNOdd`** (arm64): `z.expNNOdd(stk, x, y, m)` returns `x^y mod m` (see `Pre`/`Post`) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHyp impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW4 : nsD.contains Extracted.seg34.name = false) (hnsW2 : nsD.contains Extracted.seg35.name = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD ≤ K) (hKL : 4256 ≤ K)
    (zp zl zc st xp xl xc yp ylen yc mp n mc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 ylen, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc]
      (Pre R b L K costF zp zc st xp xl xc yp ylen mp n mc) (Post R b L K costF zp zc st xp xl yp ylen mp n) := by
  rw [show names = LibOdd.names from rfl, ← LibOdd.eq_only, show segAddr Extracted.program fn = fnO by decide]
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hP, hstnz, hMo, hM1, hslen, hbud⟩ := hpre
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, -, hal, hK, hK', hsp2, hacc, -, -, -, -⟩, -, -, -, -, -, -, -, -, hmO, -, -, -, hyO,
    -, -, -, -, hyl', -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  generalize hspd : s.sp.toNat - 1056 = sp at hP hs1 hK' hsp2 hacc hg3 hstw hal hmO hyO
  generalize hgd : (s.regs 28).toNat = g at hP hs28 hg1 hg2 hg3
  have hr48 := hret.user
  refine returns_of_reaches (pro impl ret hret _ sp g ylen ret (s.regs 29) s.mem hal (by omega) hsp2
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hyl' hr48 s h_pc hs1 h_x8 hs28 rfl
    h_lr rfl ?K4 ?K2)
  case K4 =>
    intro hy S M' c1 c2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 c4 c5 c6 c7 hF hrg q29 q30
    subst c7
    have hFw : MemFrame s.mem S.mem [(sp - K, sp + 1168)] :=
      hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hE := epre4 hP hFw c2 c5 hrg
    have hS := hypSumO hap w_sub (ExpW4.ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF hDiv hnsD hnsW4 b L K
      hKD hKL zp zl zc st xp xl xc yp ylen yc mp n mc)
    rw [show segAddr Extracted.program ExpW4.fn = 1798512 by decide] at hS
    have hSsp : S.sp.toNat = sp + 928 := by rw [c2]; exact tN (by omega)
    have hSg : (S.regs 28).toNat = g := by rw [c5, hs28]; exact tN (by omega)
    have rd : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1168) → S.mem.readLE a k = s.mem.readLE a k :=
      fun h => hF.readLE _ _ (out_win h hK')
    have el : stLen S.mem st = stLen s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
    refine Reaches.call_regions (hS.withExit hret) c1 ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg' => ?_)
    case ra => rw [c6, tN (by decide)]; exact ra4 impl hap
    case args =>
      simp only [ArgsFrom]
      exact ⟨d0.trans h_x0, d1.trans h_x1, d2.trans h_x2,
        d3.trans h_x3, d4.trans h_x4, d5.trans h_x5,
        d6.trans h_x6, d7.trans h_x7, d8.trans h_x8,
        d9.trans h_x9, d10.trans h_x10, d11.trans h_x11,
        d12.trans h_x12, trivial⟩
    case pre =>
      unfold ExpW4.Pre ExpW4.PreD
      rw [hSsp, hSg, show sp + 928 - 928 = sp by omega, el, show natVal S.mem mp n = natVal s.mem mp n from rd hmO.2.1]
      refine ⟨hE, hstnz, hMo, hM1, hslen, ?_⟩
      unfold OBud at hbud; rw [if_pos hy] at hbud; exact hbud
    unfold ExpW4.Post ExpW4.PostD at hq
    have hq' := hq
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFq, -⟩ := hq'
    have hsp' : s'.sp = BitVec.ofNat 64 (sp + 928) := e1.trans c2
    have q29' : s'.mem.readLE (sp + 920) 8 = (s.regs 29).toNat := by
      rw [hFq.readLE _ _ (slot_keep hP hF hSsp (Nat.le_refl _) (Or.inl rfl))]; exact q29
    have q30' : s'.mem.readLE (sp + 928) 8 = ret := by
      rw [hFq.readLE _ _ (slot_keep hP hF hSsp (Nat.le_refl _) (Or.inr rfl))]; exact q30
    have hacc' : s'.mem.accessible (sp + 920) 16 false = true := by
      rw [hFq.accessible, hF.accessible]
      exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
    refine epi impl ret hret _ sp (s.regs 29).toNat 1798404 s'.mem (Or.inl rfl) hal (by omega) hsp2 hacc' q29' q30' s'
      (hr.trans c6) hsp' rfl fun s'' f1 f2 f3 f4 f5 f6 f7 f8 => ⟨⟨f1.trans hs1.symm, f7.trans (e2.trans c5),
        f2.trans (FvModexp.Expmc.bv_ofNat_toNat _), f6.trans (e4.trans c4)⟩, ?_⟩
    exact post_gen hP hF hSsp (Nat.le_refl _) c5 (Or.inr (by unfold OCost; rw [if_pos hy])) hq f3 f4 f5 f8
  case K2 =>
    intro hy S M' c1 c2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 c4 c5 c6 c7 hF hrg q29 q30
    subst c7
    have hFw : MemFrame s.mem S.mem [(sp - K, sp + 1168)] :=
      hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hE := epre2 hP hFw (by rw [show sp + 288 + 640 = sp + 928 by omega]; exact c2) c5 hrg
    have hS := hypSumO hap w_sub (ExpW2.ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF hDiv hnsD hnsW2 b L (K + 288)
      (by omega) (by omega) zp zl zc st xp xl xc yp ylen yc mp n mc)
    rw [show segAddr Extracted.program ExpW2.fn = 1801904 by decide] at hS
    have hSsp : S.sp.toNat = sp + 928 := by rw [c2]; exact tN (by omega)
    have hSg : (S.regs 28).toNat = g := by rw [c5, hs28]; exact tN (by omega)
    have rd : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1168) → S.mem.readLE a k = s.mem.readLE a k :=
      fun h => hF.readLE _ _ (out_win h hK')
    have el : stLen S.mem st = stLen s.mem st := rd (ap_sub1 hstw (by omega) (by omega))
    refine Reaches.call_regions (hS.withExit hret) c1 ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg' => ?_)
    case ra => rw [c6, tN (by decide)]; exact ra2 impl hap
    case args =>
      simp only [ArgsFrom]
      exact ⟨d0.trans h_x0, d1.trans h_x1, d2.trans h_x2,
        d3.trans h_x3, d4.trans h_x4, d5.trans h_x5,
        d6.trans h_x6, d7.trans h_x7, d8.trans h_x8,
        d9.trans h_x9, d10.trans h_x10, d11.trans h_x11,
        d12.trans h_x12, trivial⟩
    case pre =>
      unfold ExpW2.Pre ExpW2.PreD
      rw [hSsp, hSg, show sp + 928 - 640 = sp + 288 by omega, el, show natVal S.mem mp n = natVal s.mem mp n from rd hmO.2.1]
      refine ⟨hE, hstnz, hMo, hM1, by simp only [StackNat.rnd] at hslen ⊢; omega, ?_⟩
      unfold OBud at hbud; rw [if_neg (by omega)] at hbud; exact hbud
    unfold ExpW2.Post ExpW2.PostD at hq
    have hq' := hq
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFq, -⟩ := hq'
    have hsp' : s'.sp = BitVec.ofNat 64 (sp + 928) := e1.trans c2
    have q29' : s'.mem.readLE (sp + 920) 8 = (s.regs 29).toNat := by
      rw [hFq.readLE _ _ (slot_keep hP hF hSsp (by omega) (Or.inl rfl))]; exact q29
    have q30' : s'.mem.readLE (sp + 928) 8 = ret := by
      rw [hFq.readLE _ _ (slot_keep hP hF hSsp (by omega) (Or.inr rfl))]; exact q30
    have hacc' : s'.mem.accessible (sp + 920) 16 false = true := by
      rw [hFq.accessible, hF.accessible]
      exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
    refine epi impl ret hret _ sp (s.regs 29).toNat 1798420 s'.mem (Or.inr rfl) hal (by omega) hsp2 hacc' q29' q30' s'
      (hr.trans c6) hsp' rfl fun s'' f1 f2 f3 f4 f5 f6 f7 f8 => ⟨⟨f1.trans hs1.symm, f7.trans (e2.trans c5),
        f2.trans (FvModexp.Expmc.bv_ofNat_toNat _), f6.trans (e4.trans c4)⟩, ?_⟩
    exact post_gen hP hF hSsp (by omega) c5 (Or.inr (by unfold OCost; rw [if_neg (by omega)])) hq f3 f4 f5 f8

end FvModexp.Arm64.ExpOdd
