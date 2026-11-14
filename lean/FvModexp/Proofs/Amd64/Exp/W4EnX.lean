import FvModexp.Proofs.Amd64.Exp.W4EnCtx
import FvModexp.Proofs.Amd64.Exp.W4XnS

set_option autoImplicit false

/-!
# window-4 entry (amd64): at `xnE` (after the inline `stk.reserve`) → the function's `RET` (= `ctxX_of` + `xnStep`)
(agent expmc s57; twin of `Arm64.W4EnX`)

`XnB`: the level / budget side conditions of `W4Pro.xnStep` at the level `l` (both `x` normalisation paths), bundled;
monotone in the budget.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4En

open FvModexp.Amd64.W4Pro (XnQ XjL xjBud)

/-- the level / budget side conditions of `xnStep` at the level `l` (budget `b`) -/
@[reducible] def XnB (costF : Nat → Nat → Nat → Nat) (n costD l xl b : Nat) : Prop :=
  XjL costF n costD l ∧ XjL costF n costD (l + StackNat.rnd n) ∧ xjBud n costD l ≤ b ∧
  stackNatCost l n + xjBud n costD (l + StackNat.rnd n) ≤ b ∧
  l + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + 64 ≤ 2 ^ 16 ∧
  costF (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n ≤ costD ∧
  XjL costF n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n) ∧
  XjL costF n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n) ∧
  stackNatCost l (xl - n + 1) + (stackNatCost (l + StackNat.rnd (xl - n + 1)) n +
    (costD + xjBud n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n))) ≤ b ∧
  stackNatCost l (xl - n + 1) + (stackNatCost (l + StackNat.rnd (xl - n + 1)) n +
    (costD + (stackNatCost (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n) n +
      xjBud n costD (l + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n)))) ≤ b

theorem XnB.mono {costF : Nat → Nat → Nat → Nat} {n costD l xl b b' : Nat} (h : XnB costF n costD l xl b)
    (hb : b ≤ b') : XnB costF n costD l xl b' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  exact ⟨a1, a2, by omega, by omega, a5, a6, a7, a8, by omega, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem atXnE (hRR : FvModexp.Amd64.W4Pro.RRSpec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    {nsD : List String} {stkD costD : Nat} {costF : Nat → Nat → Nat → Nat}
    (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true) (hnsW : nsD.contains W4Loop.fn = false)
    {nsL : List String} {stkL : Nat} (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true) (hnsWL : nsL.contains W4Loop.fn = false)
    {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc s) (hstnz : st ≠ 0)
    (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1) (hM1 : 1 < s.mem.readLE mp (8 * n))
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hF : MemFrame s.mem M (R.rt ++ [(sp - 8 - K, sp + 0x3f8), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hkf : ArrKF R L st s.mem M) (hlen : stLen M st = stLen s.mem st + StackNat.rnd (23 * n))
    (hcap : stLen M st ≤ stCap M st) (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hsl : ESl M sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st))
    (hB : XnB costF n costD (stLen s.mem st + StackNat.rnd (23 * n)) xl b1)
    (hinv1 : R.inv b1 L1 g (view R.rt L1 M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xnE) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (XnQ R b1 costD L1 g fs sp K n mp (s.mem.readLE mp (8 * n)) yp ylen (s.mem.readLE yp (8 * ylen))
        (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen s.mem st + StackNat.rnd (23 * n)) bp xl
        (s.mem.readLE xp (8 * xl)) M) := by
  obtain ⟨hC, hxs, hacc2, hxi, hxN, hxr⟩ := ctxX_of hP hstnz hF hLF hrg hx hkf hlen hcap hc40 hnl hsl
  rw [hlen] at hC hxs hxi
  have hP' := hP
  obtain ⟨he, hgl, hwt, hadx, hn, hn128, hmc, hmc', hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, hyl',
    hxO, hxa, hx48, hxN0, hxl, hxl', hxlc, hxc, hzp, hzc, hz, hgO, hsok, hstw, hstg, hstfs, harr, hwbA, hstf, hl16,
    hbp, hr388, hr47, r390, r398, r3a8, r3b0, r3b8, hinv⟩ := hP'
  have hro := he.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsv := he.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, q10, q11, q12, -, -, -, -, -⟩ := hsl
  obtain ⟨b1', b2', b3', b4', b5', b6', b7', b8', b9', b10'⟩ := hB
  rw [← hxr]
  exact W4Pro.xnStep hRR hap hclr hmv hmk (by rw [show NatSub.wordT = wTy from rfl]; exact hwt) hro hSN hsv hDiv hnsD hnsW hLsh hnsL hnsWL (fbp := bp) hKD hKL hC hlen hxi
    hxN (by omega) hxs hacc2 q10 q11 q12 (by rw [← hbp]; exact BitVec.isLt _) (FvModexp.Expmc.readLE_lt_B _ _ _)
    hMo hM1 b1' b2' b3' b4' b5' b6' b7' b8' b9' b10' hinv1 S hpc hsp hmem h6 h8 h9 h7 h3 h14 hfs hx15 hdf

end FvModexp.Amd64.W4En
