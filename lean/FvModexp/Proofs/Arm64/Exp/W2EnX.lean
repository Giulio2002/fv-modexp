import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2EnCtx
import FvModexp.Proofs.Arm64.Exp.W2XnS

/-!
# window-2 entry (arm64): at `xnE` (after the inline `stk.reserve`) → the function's `RET` (= `ctxB_of` + `xnStep`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2En

open FvModexp.Arm64.W2Pro (XnPost xjBud xnBudA xnBudAC)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem atXnE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg35.name = false)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp ylen mp n mc : Nat) (s : State)
    (r18 r29 f29 : BitVec 64)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s) (hstnz : st ≠ 0) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1) (hM1 : 1 < s.mem.readLE mp (8 * n))
    (hslen : stLen s.mem st + StackNat.rnd (11 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl +
      StackNat.rnd n + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16)
    (hcs : W2Pro.DivCosts costF costD n xl (stLen s.mem st + StackNat.rnd (11 * n)))
    (hbC : stackNatCost (stLen s.mem st) (11 * n) + xjBud n costD (stLen s.mem st + StackNat.rnd (11 * n)) ≤ b)
    (hbB : stackNatCost (stLen s.mem st) (11 * n) + (stackNatCost (stLen s.mem st + StackNat.rnd (11 * n)) n +
      xjBud n costD (stLen s.mem st + StackNat.rnd (11 * n) + StackNat.rnd n)) ≤ b)
    (hbA : stackNatCost (stLen s.mem st) (11 * n) +
      xnBudA n costD (stLen s.mem st + StackNat.rnd (11 * n)) (xl - n + 1) ≤ b)
    (hbAC : stackNatCost (stLen s.mem st) (11 * n) +
      xnBudAC n costD (stLen s.mem st + StackNat.rnd (11 * n)) (xl - n + 1) ≤ b)
    (hbP : stackNatCost (stLen s.mem st) (11 * n) +
      W2Pro.xnPre n costD (stLen s.mem st + StackNat.rnd (11 * n)) (xl - n + 1) ≤ b)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat)
    (hF : MemFrame s.mem M (R.rt ++ [(sp - K, sp + 752), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hkf : ArrKF R L st s.mem M) (hlen : stLen M st = stLen s.mem st + StackNat.rnd (11 * n))
    (hcap : stLen M st ≤ stCap M st) (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hsl : ESl M sp st r29 ret zp zc xp xl xc yp ylen mp n mc (stLen s.mem st))
    (hb1 : b - stackNatCost (stLen s.mem st) (11 * n) ≤ b1) (hinv1 : R.inv b1 L1 g (view R.rt L1 M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xnE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h8 : S.regs 8 = BitVec.ofNat 64 ylen) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ Xv', Xv' % s.mem.readLE mp (8 * n) = s.mem.readLE xp (8 * xl) % s.mem.readLE mp (8 * n) ∧
        Xv' < Exp.B ^ n ∧
        XnPost R L1 K (b1 - W2Pro.xnPre n costD (stLen s.mem st + StackNat.rnd (11 * n)) (xl - n + 1)) M g sp n mp mc (s.mem.readLE mp (8 * n)) Xv' yp ylen (s.mem.readLE yp (8 * ylen))
          (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen s.mem st + StackNat.rnd (11 * n))
          r18 r29 s')) := by
  have hC := ctxB_of hP hstnz hF hLF hrg hx hkf hlen hcap hc40 hnl hsl
  rw [hlen] at hC
  have hP' := hP
  obtain ⟨he, -, -, -, -, -, hn128, -, -, -, -, -, -, -, -, -, -, -, -,
    hxO, hxa, hx48, hxN, hxl, hxl', hxp, hxc, -⟩ := hP'
  have hsv := he.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hl0 : stLen s.mem st ≤ stLen M st := by omega
  have hrd := fun {a' k' : Nat} (h1 : xp ≤ a') (h2 : a' + k' ≤ xp + 8 * xl) => rd_of_OE hxO hF hLF h1 h2
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17⟩ := hsl
  refine W2Pro.xnStep impl hap R hclr hmv hmk hSN nsD stkD costD costF hDiv hnsD hnsW nsL stkL hLsh hnsL hnsWL hsv ret hret b1 L1
    g sp K n mp mc (s.mem.readLE mp (8 * n)) (s.mem.readLE xp (8 * xl)) yp ylen (s.mem.readLE yp (8 * ylen))
    (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen s.mem st + StackNat.rnd (11 * n)) xp xl xc
    M r18 r29 f29 hKD hKL hC hlen ?_ (by rw [hF.accessible]; exact hxa) hx48 ?_ hxl hxl' hxc
    (hrd (Nat.le_refl _) (Nat.le_refl _)) (FvModexp.Expmc.readLE_lt_B _ _ _) hMo hM1 hslen hcs (by omega) (by omega)
    (by omega) (by omega) hinv1 q10 q11 q12 L1 _ M (W2Pro.Anc.refl R L1 sp K st M)
    (W2Pro.bP (W2Pro.xnPre_ge1 _ _ _ _) hbP hb1) (W2Pro.bP (W2Pro.xnPre_ge2 _ _ _ _) hbP hb1)
    (W2Pro.bP (W2Pro.xnPre_ge3 _ _ _ _) hbP hb1) (W2Pro.bP (W2Pro.xnPre_ge4 _ _ _ _) hbP hb1) (Nat.le_of_eq hlen) S hpc hsp h3 h4 h5 h6 h8 h10 h11 h18 h28 h29 hmem
  · have := obj_of_OE hxO hx hkf hl0 hcap; rwa [hlen] at this
  · rcases hxN with h | h
    · exact Or.inl h
    · right; rw [hrd (by omega) (by omega)]; exact h

end FvModexp.Arm64.W2En
