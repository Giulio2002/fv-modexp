import FvModexp.Proofs.Arm64.Exp.MulHypR

/-!
# Export shapes of `nat.sqr` / `nat.mul` (arm64; owner divmc) — infra's `SqrHypR` / `MulHypR` + the facts the proofs need

`SqrHypX` / `MulHypX` = `EvenHyp.SqrHypR` / `MulHypR` with
* one more pre conjunct `SqrX` / `MulX`: the stack object is non-nil; its free part is held, outside the callee window,
  apart from the `stackguard0` word, the header, the threshold globals `gA` (read by inner calls AFTER `z`/the stack
  were written); the header is apart from `runtime.writeBarrier` and `gA`; `z` is outside the window even when empty;
  a `z` sharing an operand's array shares its capacity (Go's `alias` compares the cap ends); `z` and the operands are
  apart from the free part and from `gA` (`OpX`);
* the post in the `StackBackL` form (`SqrPostL` / `MulPostL`: a new stack array is an exact element of the final live
  set — coordinator's STACK-IN-LIVE-SET DECISION), `toPost` gives infra's `SqrPost` / `MulPost` back.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.ExpHyp (NatOF RtPost stWs)

/-- the stack object's free part `[w + 8·len, w + 8·cap)` -/
@[reducible] def frP (m : Memory) (st : Nat) : Nat := stW m st + 8 * stLen m st
@[reducible] def frN (m : Memory) (st : Nat) : Nat := 8 * (stCap m st - stLen m st)

/-- the extra stack facts (see the module doc) -/
@[reducible] def StkX (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st : Nat) : Prop :=
  st ≠ 0 ∧ Apart st 24 StackNat.wbA 4 ∧ Held R L (frP s.mem st) (frN s.mem st) ∧
    Outside (frP s.mem st) (frN s.mem st) (win s stk above) ∧
    Apart (frP s.mem st) (frN s.mem st) ((s.regs 28).toNat + 16) 8 ∧ Apart st 24 (frP s.mem st) (frN s.mem st) ∧
    Apart st 24 RunIface.gA 32 ∧ Apart (frP s.mem st) (frN s.mem st) RunIface.gA 32

/-- an array `[p, p + n)` apart from the free part and the threshold globals -/
@[reducible] def OpX (m : Memory) (st p n : Nat) : Prop :=
  0 < n → Apart p n (frP m st) (frN m st) ∧ Apart p n RunIface.gA 32

@[reducible] def SqrX (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st zp zc x xl xc : Nat) : Prop :=
  StkX R L s stk above st ∧ Outside zp (8 * zc) (win s stk above) ∧ (zp = x → zc = xc) ∧
    OpX s.mem st zp (8 * zc) ∧ OpX s.mem st x (8 * xl)

@[reducible] def MulX (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above st zp zc x xl xc y yl yc : Nat) :
    Prop :=
  StkX R L s stk above st ∧ Outside zp (8 * zc) (win s stk above) ∧ (zp = x → zc = xc) ∧ (zp = y → zc = yc) ∧
    OpX s.mem st zp (8 * zc) ∧ OpX s.mem st x (8 * xl) ∧ OpX s.mem st y (8 * yl)

/-- `SqrPost` with the stack in the `StackBackL` form -/
@[reducible] def SqrPostL (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zc st x xl : Nat)
    (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (2 * xl) p' l' c' (natVal s.mem x xl * natVal s.mem x xl) ∧
      RtPost R b c L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (p' = zp ∧ c' = zc) → 0 < c' → 0 < stCap s'.mem st → Apart p' (8 * c') (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

theorem SqrPostL.toPost {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {stk above zp zc st x xl : Nat}
    {s s' : State} (h : SqrPostL R b c L stk above zp zc st x xl s s') : SqrPost R b c L stk above zp zc st x xl s s' := by
  obtain ⟨p', l', c', h0, h1, h2, L', b', h3, h4, h5, h6⟩ := h
  exact ⟨p', l', c', h0, h1, h2, L', b', h3, h4, h5.1, h6⟩

/-- `MulPost` with the stack in the `StackBackL` form -/
@[reducible] def MulPostL (R : RtInv) (b c : Nat) (L : List (Nat × Nat)) (stk above zp zc st x xl y yl : Nat)
    (s s' : State) : Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatOF R L L' s'.mem zp zc (xl + yl) p' l' c' (natVal s.mem x xl * natVal s.mem y yl) ∧
      RtPost R b c L L' b' s s' ∧ StackBackL R L L' st s.mem s'.mem ∧
      (¬ (p' = zp ∧ c' = zc) → 0 < c' → 0 < stCap s'.mem st → Apart p' (8 * c') (stW s'.mem st) (8 * stCap s'.mem st)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)

theorem MulPostL.toPost {R : RtInv} {b c : Nat} {L : List (Nat × Nat)} {stk above zp zc st x xl y yl : Nat}
    {s s' : State} (h : MulPostL R b c L stk above zp zc st x xl y yl s s') :
    MulPost R b c L stk above zp zc st x xl y yl s s' := by
  obtain ⟨p', l', c', h0, h1, h2, L', b', h3, h4, h5, h6⟩ := h
  exact ⟨p', l', c', h0, h1, h2, L', b', h3, h4, h5.1, h6⟩

def SqrHypX (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSqr) [z, zl, zc, st, x, xl, xc]
      (fun s => SqrPre R b (cost (stLen s.mem st.toNat) xl.toNat) L stk above z.toNat zl.toNat zc.toNat st.toNat x.toNat
        xl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        SqrX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat)
      (fun s s' => SqrPostL R b (cost (stLen s.mem st.toNat) xl.toNat) L stk above z.toNat zc.toNat st.toNat x.toNat
        xl.toNat s s' ∧ Reuse (2 * xl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat)] s')

def MulHypX (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat)
      (fun s s' => MulPostL R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zc.toNat st.toNat
        x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

end FvModexp.Arm64.EvenHyp
