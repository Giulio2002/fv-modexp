import FvModexp.Proofs.Amd64.Exp.W4EnA
import FvModexp.Proofs.Amd64.Exp.W4EnG2
import FvModexp.Proofs.Amd64.Exp.W4EnJ
import FvModexp.Proofs.Amd64.Exp.W4EnX

set_option autoImplicit false

/-!
# window-4 (amd64): from the function's entry to its `RET` (= `enA` + (`enG2`) + `enJn` + `atXnE`)
(agent expmc s57; twin of `Arm64.W4En`)

`EnPost`: the memory `M` at `xnE` (after the inline `stk.reserve(23n)`, the anchor of `W4Pro.Anc`) with its frame from
the entry memory, every fact `ctxX_of` needs (so `W4Fun` can rebuild `CtxX` at `M`), and `W4Pro.XnQ` anchored at `M`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4En

open FvModexp.Amd64.W4Pro (XnQ)

/-- what window-4 guarantees from its entry (memory `s.mem`) on -/
@[reducible] def EnPost (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc costD : Nat) (s s' : State) : Prop :=
  ∃ (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [(sp - 8 - K, sp + 0x3f8), (st, st + 24)]) ∧
    LiveFrame s.mem M L [(st, st + 24)] ∧ M.regions = s.mem.regions ∧ LiveExt R L L1 ∧
    b - stackNatCost (stLen s.mem st) (23 * n) ≤ b1 ∧
    ArrKF R L st s.mem M ∧ ArrIn L1 st s.mem M ∧ stLen M st = stLen s.mem st + StackNat.rnd (23 * n) ∧
    stLen M st ≤ stCap M st ∧ stCap M st < 2 ^ 40 ∧ NatLive M R L1 (stW M st) (stCap M st) ∧
    ESl M sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st) ∧ R.inv b1 L1 g (view R.rt L1 M) ∧
    XnQ R b1 costD L1 g fs sp K n mp (s.mem.readLE mp (8 * n)) yp ylen (s.mem.readLE yp (8 * ylen))
      (s.mem.readLE (yp + 8 * (ylen - 1)) 8) zp zc st (stLen s.mem st) (stLen s.mem st + StackNat.rnd (23 * n)) bp xl
      (s.mem.readLE xp (8 * xl)) M s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `xnE` (any memory `M` with the entry segment's frame facts) to `EnPost` -/
theorem toPost {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    (hB : XnB costF n costD (stLen s.mem st + StackNat.rnd (23 * n)) xl
      (b - stackNatCost (stLen s.mem st) (23 * n)))
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hF : MemFrame s.mem M (R.rt ++ [(sp - 8 - K, sp + 0x3f8), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hb1 : b - stackNatCost (stLen s.mem st) (23 * n) ≤ b1)
    (hkf : ArrKF R L st s.mem M) (hai : ArrIn L1 st s.mem M) (hlen : stLen M st = stLen s.mem st + StackNat.rnd (23 * n))
    (hcap : stLen M st ≤ stCap M st) (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hsl : ESl M sp st bp r zp zc xp xl xc yp ylen mp n mc (stLen s.mem st))
    (hinv1 : R.inv b1 L1 g (view R.rt L1 M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 xnE) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (EnPost R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc costD s) :=
  ReachesRet.mono (atXnE hap hclr hmv hmk hSN hDiv hnsD hnsW hLsh hnsL hnsWL hP hstnz hKD hKL hMo hM1 hF hLF hrg hx
      hkf hlen hcap hc40 hnl hsl (hB.mono hb1) hinv1 S hpc hsp hmem h6 h8 h9 h7 h3 h14 hfs hx15 hdf)
    fun _ h => ⟨M, L1, b1, hF, hLF, hrg, hx, hb1, hkf, hai, hlen, hcap, hc40, hnl, hsl, hinv1, h⟩

end FvModexp.Amd64.W4En
