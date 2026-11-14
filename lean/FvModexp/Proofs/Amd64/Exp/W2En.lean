import FvModexp.Proofs.Amd64.Exp.W2EnA
import FvModexp.Proofs.Amd64.Exp.W2EnG2
import FvModexp.Proofs.Amd64.Exp.W2EnJ
import FvModexp.Proofs.Amd64.Exp.W2EnX

set_option autoImplicit false

/-!
# window-2 (amd64): from the function's entry to its `RET` (= `enA` + (`enG2`) + `enJn` + `atXnE`)
(agent expmc s63; ported from `Amd64.W4En`)

`EnPost`: the memory `M` at `xnE` (after the inline `stk.reserve(11n)`, the anchor of `W2Pro.Anc`) with its frame from
the entry memory, every fact `ctxX_of` needs (so `W2Fun` can rebuild `CtxX` at `M`), and `W2Pro.XnQ` anchored at `M`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2En

open FvModexp.Amd64.W2Pro (XnQ)

/-- what window-2 guarantees from its entry (memory `s.mem`) on -/
@[reducible] def EnPost (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc costD : Nat) (s s' : State) : Prop :=
  ∃ (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [(sp - 8 - K, sp + 0x2e0), (st, st + 24)]) ∧
    LiveFrame s.mem M L [(st, st + 24)] ∧ M.regions = s.mem.regions ∧ LiveExt R L L1 ∧
    b - stackNatCost (stLen s.mem st) (11 * n) ≤ b1 ∧
    ArrKF R L st s.mem M ∧ ArrIn L1 st s.mem M ∧ stLen M st = stLen s.mem st + StackNat.rnd (11 * n) ∧
    stLen M st ≤ stCap M st ∧ stCap M st < 2 ^ 40 ∧ NatLive M R L1 (stW M st) (stCap M st) ∧
    ESl M sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st) ∧ M.readLE (sp + 0x148) 8 = 5 * n ∧
    R.inv b1 L1 g (view R.rt L1 M) ∧
    XnQ R b1 costD L1 g fs sp K n mp (s.mem.readLE mp (8 * n)) yp ylen (s.mem.readLE yp (8 * ylen))
      (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen s.mem st + StackNat.rnd (11 * n)) bp xl
      (s.mem.readLE xp (8 * xl)) M s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `xnE` (any memory `M` with the entry segment's frame facts) to `EnPost` -/
theorem toPost (hRR : FvModexp.Amd64.W2Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W2Loop.fn = false)
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsWL : nsL.contains W2Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc s) (hstnz : st ≠ 0)
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1) (hM1 : 1 < s.mem.readLE mp (8 * n))
    (hB : XnB costF n costD (stLen s.mem st + StackNat.rnd (11 * n)) xl
      (b - stackNatCost (stLen s.mem st) (11 * n)))
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hF : MemFrame s.mem M (R.rt ++ [(sp - 8 - K, sp + 0x2e0), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hb1 : b - stackNatCost (stLen s.mem st) (11 * n) ≤ b1)
    (hkf : ArrKF R L st s.mem M) (hai : ArrIn L1 st s.mem M) (hlen : stLen M st = stLen s.mem st + StackNat.rnd (11 * n))
    (hcap : stLen M st ≤ stCap M st) (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hsl : ESl M sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st)) (h148 : M.readLE (sp + 0x148) 8 = 5 * n)
    (hinv1 : R.inv b1 L1 g (view R.rt L1 M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xnE) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (EnPost R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc costD s) :=
  ReachesRet.mono (atXnE hRR hap hclr hmv hmk hSN hDiv hnsD hnsW hLsh hnsL hnsWL hP hstnz hKD hKL hMo hM1 hF hLF hrg hx
      hkf hlen hcap hc40 hnl hsl h148 (hB.mono hb1) hinv1 S hpc hsp hmem h6 h8 h9 h7 h3 h14 hfs hx15 hdf)
    fun _ h => ⟨M, L1, b1, hF, hLF, hrg, hx, hb1, hkf, hai, hlen, hcap, hc40, hnl, hsl, h148, hinv1, h⟩

theorem win_sep {R : RtInv} {L : List (Nat × Nat)} {sp K lo hi : Nat}
    (hrt : Outside (sp - 8 - K) (K + 0x2e8) R.rt) (hLs : LiveSep L [(sp - 8 - K, sp - 8 + 0x2e8)]) (hK : K ≤ sp - 8)
    (h1 : sp - 8 - K ≤ lo) (h2 : hi ≤ sp + 0x2e0) (h3 : lo ≤ hi) : LiveSep [(lo, hi)] R.rt ∧ LiveSep L [(lo, hi)] := by
  refine ⟨fun r hr => ?_, liveSep_sub' hLs (by omega) (by omega)⟩
  simp only [List.mem_singleton] at hr; subst hr; exact hrt.of_sub (by simp only; omega) (by simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **window-2 from its entry to its `RET`** (amd64): stack-guard check, prologue, defer record, the inline
`stk.reserve(11n)` (`growslice` + `memclrNoHeapPointers` when the array is too small, the header stores with the write
barrier), then the rest of the function (`W2Pro.xnStep`) -/
theorem enStep (hRR : FvModexp.Amd64.W2Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W2Loop.fn = false)
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsWL : nsL.contains W2Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc s) (hstnz : st ≠ 0)
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1) (hM1 : 1 < s.mem.readLE mp (8 * n))
    (hB : XnB costF n costD (stLen s.mem st + StackNat.rnd (11 * n)) xl
      (b - stackNatCost (stLen s.mem st) (11 * n)))
    (hbS : stackNatCost (stLen s.mem st) (11 * n) ≤ b) {zl : Nat} (hzl : zl < 2 ^ 64)
    (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 st) (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl)
    (h9 : s.regs 9 = BitVec.ofNat 64 xc) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) s
      (EnPost R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc costD s) := by
  have hBb : Nonempty (XnB costF n costD (stLen s.mem st + StackNat.rnd (11 * n)) xl
      (b - stackNatCost (stLen s.mem st) (11 * n))) := ⟨hB⟩
  clear hB
  have hP' := hP
  obtain ⟨he, hgl, hwt, hadx, hn, hn128, hmc0, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl',
    hxO, hxa, hx48, hxN, hxl, hxl', hxlc, hxc, hzp, hzc, hz, hgO, hsok, hstw, hstg, hstfs, harr, hwbA, hstf, hl16,
    hbp, hr388, hr47, r390, r398, r3a8, r3b0, r3b8, hinv⟩ := hP'
  obtain ⟨hs4, hs14, hfs, hx15, hdf, hal, hK, hK20, hce, hsv⟩ := he
  have hce' := hce
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce'
  have hsok' := hsok
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok'
  unfold Apart at hstw hstg hstfs hga f6
  have hrn := rnd23_le n
  have hok : R.ok wbE [2] := by rw [← wbE_eq]; exact hsv.2.2.2.2.2.1 _
  have hwacc0 : s.mem.accessible (sp - 8 - 4096) (4096 + 8) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hwrt : Outside (sp - 8 - 4096) (4096 + 8) R.rt := hrt.of_sub (by omega) (by omega)
  have hwL : LiveSep L [(sp - 8 - 4096, sp)] := liveSep_sub' hLs (by omega) (by omega)
  have hwbf : s.mem.accessible StackNat.wbA 4 false = true := hgl.2.2.2.2.2.2.2.2.2.2.1
  have h5 : s.regs 5 = BitVec.ofNat 64 bp := by rw [← hbp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hgs : g < 2 ^ 64 := by omega
  have hwin := fun {lo hi : Nat} (h1 : sp - 8 - K ≤ lo) (h2 : hi ≤ sp + 0x2e0) (h3 : lo ≤ hi) =>
    win_sep hrt hLs hK0 h1 h2 h3
  refine enA (M := s.mem) (w0 := stW s.mem st) (len0 := stLen s.mem st) (cap0 := stCap s.mem st) hal (by omega)
    (by omega) (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega)
    (Janus.Arm64.Memory.accessible_weaken _ k3) k4 (by omega) rfl rfl rfl (by omega) k7 k6 hn128 (by omega) hzl
    (by omega) (by omega) (by omega) (by omega) (by rw [← hbp]; exact BitVec.isLt _) hr388 r390 r398 r3a8 r3b0 r3b8 s
    hpc hs4 rfl h0 h3 h1 h7 h6 h8 h9 h5 hs14 hx15 ?KJ ?KG
  case KJ =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 cm hF1 hrg1 hsl1 q148
    have hF1' : MemFrame s.mem M1 [(sp - 8 - K, sp + 0x2e0)] := hF1.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hinvM1 : R.inv b L g (view R.rt L M1) := RtInv.inv_frame hF1' (hwin (by omega) (by omega) (by omega)).1 hinv
    refine enJn hwb (b1 := b) (L1 := L) (w1 := stW s.mem st) (len0 := stLen s.mem st) (c1 := stCap s.mem st)
      (M := M1) (by omega) (by omega) hal (by rw [hF1.accessible]; exact hwacc0) hwrt hwL
      (by rw [hF1.accessible]; exact k3) k4 k2 (by omega) (by rw [hF1.accessible]; exact hwbf) hwbA hok hinvM1 hgs hk k7
      (Janus.Arm64.Memory.readLE_lt _ _ _) (by omega) hn128 S1 c1 c2 c4 c13 c9 c10 c11 c14 cm ?_
    intro S3 M3 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 dm hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - 8 - K, sp + 0x2e0), (st, st + 24)]) := by
      refine MemFrame.trans hF1 hF3 fun a k ho => ⟨?_, ?_⟩ <;>
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      · omega
      · exact ⟨ho.1, by omega, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] :=
      (LiveFrame.of_win hF1' (hwin (by omega) (by omega) (by omega)).2).trans hLF3 fun _ _ h => h
    have hsl3 : ESl M3 sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st) := by
      refine ESl.keep hsl1 (fun a ha => hF3.readLE a 8 ?_)
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩
    have h148 : M3.readLE (sp + 0x148) 8 = 5 * n := by
      rw [hF3.readLE _ 8 (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩)]
      exact q148
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hk ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact k7
    have hnl3 : NatLive M3 R L (stW M3 st) (stCap M3 st) := by
      intro hc
      simp only [stW, stCap] at q1 q3 hc ⊢
      rw [q3] at hc; rw [q1, q3]
      obtain ⟨a1, a2, a3, a4⟩ := k5 hc
      exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
    exact toPost hRR hap hclr hmv hmk hSN hDiv hnsD hnsW hLsh hnsL hnsWL hP hstnz hKD hKL hMo hM1 (hBb.elim id) hF hLF
      (hrg3.trans hrg1) (LiveExt.refl R L) (Nat.sub_le _ _) (Or.inl ⟨q1, q3⟩) (W2Pro.arrIn_kept ⟨q1, q3⟩) q2 hcap3
      hc3 hnl3 hsl3 h148 hinv3 S3 d1 d2 dm (d5.trans c5) (d6.trans c6) (d7.trans c7) d3 (d4.trans c8) d9
      (by rw [d10, c15]; exact hfs) (d11.trans c16) (d12.trans (c17.trans hdf))
  case KG =>
    intro hk S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 cm hF1 hrg1 hsl1 s148 sret s140 sb8 sd0
    have hF1' : MemFrame s.mem M1 [(sp - 8 - K, sp + 0x2e0)] := hF1.mono fun a k ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hinvM1 : R.inv b L g (view R.rt L M1) := RtInv.inv_frame hF1' (hwin (by omega) (by omega) (by omega)).1 hinv
    have hce1 : CallW.CEnv R L g fs (sp - 8) K 0x2e8 M1 :=
      CallW.CEnv.frame hce (hF1'.mono fun a k ho => by rw [outside_append] at ho; exact ho.2) hrg1
        (fun r hr _ => by
          simp only [List.mem_singleton] at hr; subst hr; simp only
          rw [show sp + 0x2e0 - (sp - 8 - K) = K + 0x2e8 by omega]; exact hacc)
        (by simp only [outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hcostG : 8 * growCap8 (stLen s.mem st + StackNat.rnd (11 * n)) (stCap s.mem st) ≤
        stackNatCost (stLen s.mem st) (11 * n) := growRound_le_cost _ _ _ hk
    have hgcl := le_growCap8 (stLen s.mem st + StackNat.rnd (11 * n)) (stCap s.mem st)
    have hgcb := growCap_lt (stLen s.mem st) (11 * n) (stCap s.mem st) hk (by omega)
    have hsl1' := hsl1
    obtain ⟨-, -, -, -, -, -, -, -, a9, a10, a11, a12, -, -, -, a16, -⟩ := hsl1'
    refine enG2 hgr hmc (b := b) (L := L) (fs := fs) (K := K) (M := M1) hce1 (by omega) hsv hk hn128 (by omega) k7
      (Janus.Arm64.Memory.readLE_lt _ _ _) ?hold (by omega) hinvM1 S1 c1 c2 c9 c3 c11 (c12.trans hdf) c4 c5 c6 c7 c8 cm
      sret sd0 sb8 s140 a9 a10 a11 a12 a16 s148 ?K2
    case hold =>
      intro hc
      obtain ⟨-, -, a3, a4⟩ := k5 hc
      obtain ⟨b1, -, -⟩ := harr hc
      exact ⟨a4, by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ a3, b1⟩
    case K2 =>
    intro S2 M2 p gc d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 dm hgc hpin hapL hp8 hp48 hpacc hF2 hLF2
      hrg2 hinv2
    subst hgc
    generalize growCap8 (stLen s.mem st + StackNat.rnd (11 * n)) (stCap s.mem st) = gc at *
    have hx : LiveExt R L (L ++ [(p, p + 8 * gc)]) :=
      ⟨[(p, p + 8 * gc)], rfl, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only [Nat.add_sub_cancel_left]; exact ⟨hpin, hapL⟩,
        List.pairwise_singleton _ _⟩
    have hpw := hpin.apart hrt
    unfold Apart at hpw
    have hF12 : MemFrame s.mem M2 (R.rt ++ [(sp - 8 - K, sp + 0x2e0)]) := by
      refine MemFrame.trans hF1 hF2 fun a k ho => ⟨?_, ?_⟩ <;>
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      · omega
      · exact ⟨ho.1, by omega, by omega, by omega⟩
    have hgs1 : LiveSep (L ++ [(p, p + 8 * gc)]) [(sp - 8 - 4096, sp)] :=
      hx.liveSep hwL fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        exact hrt.of_sub (by omega) (by omega)
    refine enJn hwb (b1 := b - 8 * gc) (L1 := L ++ [(p, p + 8 * gc)]) (w1 := p) (len0 := stLen s.mem st) (c1 := gc)
      (M := M2) (by omega) (by omega) hal (by rw [hF12.accessible]; exact hwacc0) hwrt hgs1
      (by rw [hF12.accessible]; exact k3) k4 (hx.held k2) (by omega) (by rw [hF12.accessible]; exact hwbf) hwbA hok
      hinv2 hgs hgcl hgcb (by omega) (by omega) hn128 S2 d1 d2 d4 d13 d9 d10 d11 d14 dm ?_
    intro S3 M3 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 em hF3 hLF3 hrg3 hinv3 q1 q2 q3
    have hF : MemFrame s.mem M3 (R.rt ++ [(sp - 8 - K, sp + 0x2e0), (st, st + 24)]) := by
      refine MemFrame.trans hF12 hF3 fun a k ho => ⟨?_, ?_⟩ <;>
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      · exact ⟨ho.1, ho.2.1⟩
      · exact ⟨ho.1, ho.2.2, by omega⟩
    have hLF : LiveFrame s.mem M3 L [(st, st + 24)] :=
      ((LiveFrame.of_win hF1' (hwin (by omega) (by omega) (by omega)).2).trans
        ⟨fun a k hin _ => hLF2.readLE a k hin trivial⟩ fun _ _ h => h).trans hLF3 fun a k h => hx.inRanges_old h
    have hsl3 : ESl M3 sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st) := by
      refine ESl.keep (ESl.keep hsl1 (fun a ha => hF2.readLE a 8 ?_)) (fun a ha => hF3.readLE a 8 ?_)
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩
    have h148 : M3.readLE (sp + 0x148) 8 = 5 * n := by
      rw [hF3.readLE _ 8 (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩),
        hF2.readLE _ 8 (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩)]
      exact s148
    have hcap3 : stLen M3 st ≤ stCap M3 st := by simp only [stLen, stCap] at q2 q3 hgcl ⊢; omega
    have hc3 : stCap M3 st < 2 ^ 40 := by simp only [stCap] at q3 ⊢; rw [q3]; exact hgcb
    have hgc0 : 0 < gc := by have := rnd23_pos n hn; omega
    have hkf : ArrKF R L st s.mem M3 := Or.inr (by simp only [stW, stCap] at q1 q3 ⊢; rw [q1, q3]; exact ⟨hpin, hapL⟩)
    have hai : ArrIn (L ++ [(p, p + 8 * gc)]) st s.mem M3 := fun _ => by
      simp only [stW, stCap] at q1 q3 ⊢; rw [q1, q3]; exact ⟨List.mem_append_right _ (List.mem_singleton_self _), hgc0⟩
    have hnl3 : NatLive M3 R (L ++ [(p, p + 8 * gc)]) (stW M3 st) (stCap M3 st) := by
      intro _
      simp only [stW, stCap] at q1 q3 ⊢
      rw [q1, q3]
      exact ⟨hp8, Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by simp only; omega,
        by simp only; omega⟩, by rw [hF3.accessible]; exact hpacc, hp48⟩
    exact toPost hRR hap hclr hmv hmk hSN hDiv hnsD hnsW hLsh hnsL hnsWL hP hstnz hKD hKL hMo hM1 (hBb.elim id) hF hLF
      (hrg3.trans (hrg2.trans hrg1)) hx (Nat.sub_le_sub_left hcostG _) hkf hai q2 hcap3 hc3 hnl3 hsl3 h148 hinv3 S3 e1 e2
      em (e5.trans d5) (e6.trans d6) (e7.trans d7) e3 (e4.trans d8) e9 (by rw [e10, d15, c10]; exact hfs)
      (e11.trans d16) (e12.trans (d17.trans (c12.trans hdf)))

end FvModexp.Amd64.W2En
