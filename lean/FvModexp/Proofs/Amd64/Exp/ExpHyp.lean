import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Common.ExpHypVal
import FvModexp.Proofs.Common.StackScr
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Amd64.Nat.Callees

/-!
# Callee premises of the exponentiation layer (amd64) — twin of `FvModexp.Arm64.ExpHyp` (+ `ExpHypL`)

`nat.div` (owner asm) as an `Ensures` premise in the CONVENTIONS §3 shape, in the `StackBack` form (`DivHyp`) and the
`StackBackL` form (`DivHypL`, BRIEF "STACK-IN-LIVE-SET"), plus the `*stack` names the windows use. Same statement as
the arm64 twin in the amd64 vocabulary: `g = R14`, the window `win s stk above` (it contains the return-address slot),
posts start with `s'.fsBase = s.fsBase ∧ s'.df = s.df` (DF CONVENTION), and the TLS slot `FS:-8` (re-read by every
ABI0 kernel) is apart from every range the callee writes (the outputs: `WrOut`; the stack header and free part: below).

amd64 ABIInternal argument passing of `z.div(stk, z2, u, v)` (13 words, 9 integer registers): `z` RAX,RBX,RCX, `stk` RDI,
`z2` RSI,R8,R9 in registers; `u` and `v` do not fit in the two remaining registers and are passed on the stack at
`RSP+8 … RSP+56` (`u` ptr/len/cap, `v` ptr/len/cap) — the precondition names those words. Results: `q` RAX,RBX,RCX
(`regs 0, 3, 1`), `r` RDI,RSI,R8 (`regs 7, 6, 8`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpHyp

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn WrOut NatRes RtPost)

/-- an old-or-fresh result nat: the caller's array `(zp, zc)` or a fresh runtime object of capacity `≥ need` -/
@[reducible] def NatOF (R : RtInv) (L L' : List (Nat × Nat)) (m' : Memory) (zp zc need p' l' c' v : Nat) : Prop :=
  natVal m' p' l' = v ∧ NatNorm m' p' l' ∧ l' ≤ c' ∧ c' < 2 ^ 40 ∧ NatLive m' R L' p' c' ∧
    ((p' = zp ∧ c' = zc) ∨ (need ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))

/-! ## The `*stack` object -/

@[reducible] def StackOK' (m : Memory) (R : RtInv) (L : List (Nat × Nat)) (st : Nat) : Prop := StkOK m R L st
@[reducible] def stWs (m : Memory) (st : Nat) : List (Nat × Nat) := stkWs m st

abbrev fnStackNat : String := StackNat.fn
abbrev StackNatHyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  StackNat.Hyp impl R ns stk above

/-! ## `z.div(stk, z2, u, v)` (natdiv.go:18) — results `q = u / v`, `r = u % v` (both normalised) -/

def fnDiv : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div"

/-- the precondition (arm64 `ExpHyp.DivPre` + the stack words of `u`, `v` and the TLS slot apart from the header and the
stack's free part) -/
@[reducible] def DivPre (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = u ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc ∧ s.mem.readLE ((s.regs 4).toNat + 32) 8 = v ∧
    s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl ∧ s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc ∧
  CallEnv R L s stk above ∧ Serves R ∧ RunIface.Globals R s.mem (win s stk above) ∧ zl ≤ zc ∧ z2l ≤ z2c ∧
    WrOut R L s stk above zp zc ∧ WrOut R L s stk above z2 z2c ∧
    RdIn R L s stk above u ul ∧ RdIn R L s stk above v vl ∧ ul ≤ 2 ^ 9 ∧ 0 < vl ∧ vl ≤ 2 ^ 9 ∧
    NatNorm s.mem u ul ∧ NatNorm s.mem v vl ∧
    StackOK' s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16 ∧ (stCap s.mem st = 0 → stW s.mem st = 0) ∧
    Apart u (8 * ul) st 24 ∧ Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    Apart v (8 * vl) st 24 ∧ Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) ∧
    st ≠ 0 ∧
    (Apart st 24 ((s.regs 14).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    (Apart st 24 (s.fsBase.toNat - 8) 8 ∧
      Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8) ∧
    (0 < zc → Apart zp (8 * zc) RunIface.gA 32) ∧ (0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32) ∧ Apart st 24 RunIface.gA 32 ∧
    Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32 ∧
    (0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)) ∧
    (∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      Apart p (8 * c) u (8 * ul) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) ∧
    cost (stLen s.mem st) ul vl ≤ b ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- the postcondition, `StackBack` form -/
@[reducible] def DivPost (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b (cost (stLen s.mem st) ul vl) L L' b' s s' ∧ StackBack R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st)

def DivHyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c]
      (fun s => DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc
        v vl vc s)
      (fun s s' => DivPost R b cost L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s')

/-- the postcondition, `StackBackL` form -/
@[reducible] def DivPostL (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (stk above zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (q ql qc r rl rc : Nat), s'.regs 0 = BitVec.ofNat 64 q ∧ s'.regs 3 = BitVec.ofNat 64 ql ∧
    s'.regs 1 = BitVec.ofNat 64 qc ∧ s'.regs 7 = BitVec.ofNat 64 r ∧ s'.regs 6 = BitVec.ofNat 64 rl ∧
    s'.regs 8 = BitVec.ofNat 64 rc ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl) ∧
      NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl) ∧
      RtPost R b (cost (stLen s.mem st) ul vl) L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap s'.mem st →
        Apart r (8 * rc) (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc), (z2, z2 + 8 * z2c)] ++ stWs s.mem st)

theorem DivPostL.toDivPost {R : RtInv} {b : Nat} {cost : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {stk above zp zc st z2 z2c u ul v vl : Nat} {s s' : State}
    (h : DivPostL R b cost L stk above zp zc st z2 z2c u ul v vl s s') :
    DivPost R b cost L stk above zp zc st z2 z2c u ul v vl s s' := by
  obtain ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb, ha, hfr, hl⟩ := h
  exact ⟨hf, hd, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, hp, hsb.toStackBack, ha, hfr, hl⟩

/-- `DivHyp` with the `StackBackL` post -/
def DivHypL (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnDiv)
      [z, zl, zc, st, z2, z2l, z2c]
      (fun s => DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc
        v vl vc s)
      (fun s s' => DivPostL R b cost L stk above z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u ul v vl s s')

theorem DivHypL.toDivHyp {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat → Nat} (h : DivHypL impl R ns stk above cost) : DivHyp impl R ns stk above cost :=
  fun b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs hpre =>
    Returns.mono (h b L z zl zc st z2 z2l z2c u ul uc v vl vc ret hret s hs hpre) fun _ h' => ⟨h'.1, h'.2.toDivPost⟩

end FvModexp.Amd64.ExpHyp
