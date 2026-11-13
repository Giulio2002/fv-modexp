import FvModexp.Proofs.Amd64.NatQ.DivHypQ

set_option autoImplicit false

/-!
# Callee premises of `nat.expNN` (amd64): `nat.rem` (asm/divmc), `nat.expNNSlow` / `nat.expNNPowerOfTwo` (infra)

amd64 twin of `FvModexp.Arm64.NHyp` (agent expmc s65). Level-cost hypotheses (ExpHyp style, CONVENTIONS §3); `nat.rem`'s
Q-form (`NHyp.RemHypQ`, NatQ/DivHypQ) bridges to `RemHyp` as on arm64 (`ExpQ/Bridge`). Same statements as the arm64
twin in the amd64 vocabulary (as `ExpHyp.DivPre`): `g = R14`, the window `win s stk above` (it contains the
return-address slot), posts start with `s'.fsBase = s.fsBase ∧ s'.df = s.df` (DF CONVENTION), the TLS slot `FS:-8`
apart from the stack header, its free part and the stack array, `hasADX` readable (`Callees.adxAddr`).

amd64 ABIInternal argument passing (9 integer registers RAX RBX RCX RDI RSI R8 R9 R10 R11; an argument that does not fit
in the remaining registers goes to the stack and later arguments still use registers), checked against
`dis/nat.expNN.amd64.s`:
* `z.rem(stk, u, v)` (fn+0x3aa): `z` RAX,RBX,RCX, `stk` RDI, `u` RSI,R8,R9; `v` at `RSP+8 … RSP+24`.
* `z.expNNSlow(stk, x, y, m)` (fn+0x5da, +0x702, +0x781): `z`, `stk`, `x` as above; `y` at `RSP+8 … +24`, `m` at
  `RSP+32 … +48`.
* `z.expNNPowerOfTwo(stk, x, y, logM)` (fn+0x8c0): `z`, `stk`, `x` as above; `y` at `RSP+8 … +24`; `logM` R10.
Results: `RAX, RBX, RCX` (`regs 0, 3, 1`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.NHyp

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn WrOut RtPost)
open FvModexp.Amd64.ExpHyp (NatOF StackOK' stWs)

/-- common entry facts of a stack-taking callee of `nat.expNN` (arm64 `NHyp.CPre` + the TLS slot and `hasADX`; the body
of `RemPreQ` without its stack words and Q extras) -/
@[reducible] def CPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc st : Nat)
    (ins : List (Nat × Nat)) (need cst : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ RoOut R ∧
    Outside StackNat.wT 16 R.rt ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧
    (∀ p n, (p, n) ∈ ins → RdIn R L s stk above p n ∧ n ≤ 2 ^ 9 ∧ NatNorm s.mem p n ∧ Apart p (8 * n) st 24 ∧
      Apart p (8 * n) (freeOf s.mem st).1 (freeOf s.mem st).2 ∧ (0 < zc → Apart zp (8 * zc) p (8 * n))) ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧ Apart st 24 ((s.regs 14).toNat + 16) 8 ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    (stCap s.mem st = 0 → stW s.mem st = 0) ∧ stLen s.mem st + need ≤ 2 ^ 16 ∧
    s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
    Apart st 24 (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
    (Apart st 24 (s.fsBase.toNat - 8) 8 ∧ Apart (freeOf s.mem st).1 (freeOf s.mem st).2 (s.fsBase.toNat - 8) 8) ∧
    (0 < zc → Apart zp (8 * zc) st 24 ∧ Apart zp (8 * zc) (freeOf s.mem st).1 (freeOf s.mem st).2 ∧
      Apart zp (8 * zc) RunIface.gA 32) ∧
    Apart st 24 RunIface.gA 32 ∧ Apart (freeOf s.mem st).1 (freeOf s.mem st).2 RunIface.gA 32 ∧
    cst ≤ b ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧
    (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (s.fsBase.toNat - 8) 8) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- common exit facts with `ResSep`: the result nat `(p, l, c)` (`RAX, RBX, RCX`) of value `v` -/
@[reducible] def CPostR (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v cst : Nat) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF R L L' s'.mem zp zc 1 p l c v ∧ RtPost R b cst L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- `ExpHyp.NatOF` with need `1` and the EMPTY result `nil` allowed (arm64 `NHyp.NatOF0`) -/
@[reducible] def NatOF0 (R : RtInv) (L L' : List (Nat × Nat)) (m' : Memory) (zp zc p' l' c' v : Nat) : Prop :=
  natVal m' p' l' = v ∧ NatNorm m' p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧ NatLive m' R L' p' c' ∧
    ((c' = 0 ∧ p' = 0) ∨ (p' = zp ∧ c' = zc) ∨ (1 ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))

/-- `CPostR` with `NatOF0` (a `nil` result allowed) -/
@[reducible] def CPostR0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v cst : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF0 R L L' s'.mem zp zc p l c v ∧ RtPost R b cst L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- the extra facts of the operand `x` of `expNNSlow` / `expNNPowerOfTwo` / `expNNEven` (arm64 `NHyp.XFacts`) -/
@[reducible] def XFacts (R : RtInv) (L : List (Nat × Nat)) (x xl xc : Nat) : Prop :=
  (xl ≤ xc ∧ xc < 2 ^ 40 ∧ (0 < xc → Held R L x (8 * xc) ∧ x + 8 * xc ≤ 2 ^ 48)) ∧
    (0 < xl → Apart x (8 * xl) RunIface.gA 32)

/-- `XFacts` survives a live-set extension -/
theorem XFacts.ext {R : RtInv} {L L' : List (Nat × Nat)} {x xl xc : Nat} (h : LiveExt R L L')
    (hx : XFacts R L x xl xc) : XFacts R L' x xl xc :=
  ⟨⟨hx.1.1, hx.1.2.1, fun hc => ⟨h.held (hx.1.2.2 hc).1, (hx.1.2.2 hc).2⟩⟩, hx.2⟩

/-- an array `(p, c)` apart from the stack's header and (non-empty) free part (arm64 `EvenHyp.StkApart`) -/
@[reducible] def StkApart (m : Memory) (st p c : Nat) : Prop :=
  0 < c → Apart p c st 24 ∧
    (stLen m st < stCap m st → Apart p c (stW m st + 8 * stLen m st) (8 * (stCap m st - stLen m st)))

/-- the three stack words `RSP+k+8 … RSP+k+24` of a nat argument passed on the stack -/
@[reducible] def StkArg (s : State) (k p l c : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + k + 8) 8 = p ∧ s.mem.readLE ((s.regs 4).toNat + k + 16) 8 = l ∧
    s.mem.readLE ((s.regs 4).toNat + k + 24) 8 = c

/-! ## `z.rem(stk, u, v)` (natdiv.go:505); result `U % V` -/

def RemHyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st u ul uc : BitVec 64) (v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnRem)
      [z, zl, zc, st, u, ul, uc]
      (fun s => StkArg s 0 v vl vc ∧
        (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(u.toNat, ul.toNat), (v, vl)]
          (need ul.toNat vl) (cost (stLen s.mem st.toNat) ul.toNat vl) s ∧ 0 < vl) ∧
        NoAlias z.toNat zc.toNat u.toNat uc.toNat ∧ 0 < st.toNat)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem u.toNat ul.toNat % natVal s.mem v vl) (cost (stLen s.mem st.toNat) ul.toNat vl) s s')

/-! ## `z.expNNSlow(stk, x, y, m)` (nat.go:732); `X ^ Y % M` -/

def fnSlow : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNSlow"

def SlowHyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSlow)
      [z, zl, zc, st, x, xl, xc]
      (fun s => (StkArg s 0 y yl yc ∧ StkArg s 24 m ml mc) ∧
        (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(x.toNat, xl.toNat), (y, yl), (m, ml)]
          (need xl.toNat yl ml) (cost (stLen s.mem st.toNat) xl.toNat yl ml) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 2 ≤ natVal s.mem y yl ∧ 0 < natVal s.mem m ml ∧
        0 < st.toNat) ∧ XFacts R L x.toNat xl.toNat xc.toNat)
      (fun s s' => CPostR0 R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y yl % natVal s.mem m ml)
        (cost (stLen s.mem st.toNat) xl.toNat yl ml) s s')

/-! ## `z.expNNPowerOfTwo(stk, x, y, logM)` (nat.go:906); `X ^ Y % 2 ^ logM`; the package global `natOne` as in the
arm64 twin -/

def fnP2 : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwo"

def P2Hyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc lm : BitVec 64) (y yl yc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnP2)
      [z, zl, zc, st, x, xl, xc, lm]
      (fun s => StkArg s 0 y yl yc ∧
        (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(x.toNat, xl.toNat), (y, yl)]
          (need xl.toNat yl lm.toNat) (cost (stLen s.mem st.toNat) xl.toNat yl lm.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 0 < natVal s.mem y yl ∧ 1 ≤ lm.toNat ∧ lm.toNat ≤ 2 ^ 13 ∧
        0 < st.toNat ∧
        ∃ op, EvenHyp.NatOne R L s.mem op (win s stk above ++ [(z.toNat, z.toNat + 8 * zc.toNat)] ++
            stWs s.mem st.toNat) ∧ StkApart s.mem st.toNat op 8) ∧ xl.toNat ≤ xc.toNat ∧ xc.toNat < 2 ^ 40)
      (fun s s' => CPostR R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y yl % 2 ^ lm.toNat)
        (cost (stLen s.mem st.toNat) xl.toNat yl lm.toNat) s s')

end FvModexp.Amd64.NHyp
