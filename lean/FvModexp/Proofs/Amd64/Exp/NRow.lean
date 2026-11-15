import FvModexp.Proofs.Amd64.Exp.NCap
import FvModexp.Proofs.Amd64.Exp.P2DRow
import FvModexp.Proofs.Amd64.Exp.SlowCl
import FvModexp.Proofs.Amd64.Exp.DivInst
import FvModexp.Proofs.Amd64.Exp.RemInst
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.NatQ.DivRowWitQ

set_option autoImplicit false

/-!
# Row: `nat.expNN` (amd64), `slow = false`, `m` odd or a power of two, on the Run extraction (agent asm s83; twin of
infra's Arm64/Exp/NRow)

`correctness` = expmc's `ExpN.ens_noEven` (inner window `K = 41640`, frame `[RSP - 0x498 - K, RSP + 0x78)`) moved to
`Extracted.program.link impl` (`Summary.of_codeIn64` + `Summary.returns`), with EVERY callee proved: `nat.div` =
`DivInst.hyp` (41512), `nat.expNNSlow` = expmc's closed `Q.ExpSlow.slowCl` (41952), `nat.expNNPowerOfTwo` =
`P2DRow.hyp` (42520), `nat.rem` = `RemInst.hyp` (41720). Runtime premises: the live `growslice`,
`memclrNoHeapPointers`, `memmove` (+ zero-length), `makeslice`, `newobject`, `gcWriteBarrier2` contracts.
The division-cost parameter `costD` of `ExpN.Pre` (the windows' budget, `ExpOdd.OBud`) is a binder of the theorem.
`y` and `m` are the stack arguments: `Pre` states them at `RSP + 8 … RSP + 48` with NUMERAL offsets (`ArgY` / `ArgM`,
the v0.3.3 audit rule) besides `ExpN.Pre`.
Release order: this row right before `amd64 Exp/EvenRow`, so EvenRow no longer compiles the expNN / expNNOdd chains
itself (EvenRow own-set cut, asm s83).
`Witness`: the call `z.expNN(stk, 3, 5, 7, false)` (`3^5 mod 7`) with `z = nil`, the stack `{w, 0, 4}`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `NPre` WITHOUT its six stack-argument reads (`sp + 0x4a0 …`, i.e. `RSP + 8 …` through `sp = RSP - 0x498`) and WITHOUT
`NEnv`'s equation `RSP = sp + 0x498` and `CEnv`'s closed bound `sp + 0x510 ≤ 2^48` (both read as RSP pins by the
audit probe; they follow from `K ≤ sp` and the window's accessibility): the row states the reads with
literal `RSP + k` offsets instead (`NRow.ArgY` / `NRow.ArgM`, the v0.3.3 audit rule), asm s83 -/
def NPreS (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat) (costD : Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  (s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧ s.xmm 15 = 0 ∧ s.df = false ∧ 41640 ≤ K ∧ K + 0x98 ≤ 2 ^ 20 ∧
    (sp % 8 = 0 ∧ K ≤ sp ∧ s.mem.accessible (sp - K) (K + 0x510) true = true ∧
    g + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (g + 16) 8 false = true ∧ s.mem.readLE (g + 16) 8 + K < sp ∧ Outside (sp - K) (K + 0x510) R.rt ∧ Apart (g + 16) 8 (sp - K) (K + 0x510) ∧ Outside (g + 16) 8 R.rt ∧ LiveSep L [(sp - K, sp + 0x510)] ∧ Extracted.program.DataLoaded s.mem ∧ RoOut R ∧ 8 ≤ fs ∧ fs ≤ 2 ^ 48 ∧ s.mem.accessible (fs - 8) 8 false = true ∧ s.mem.readLE (fs - 8) 8 = g ∧ Outside (fs - 8) 8 R.rt ∧ Apart (fs - 8) 8 (sp - K) (K + 0x510)) ∧
    RunIface.Serves R) ∧ RunIface.Globals R s.mem [(sp - K, sp + 0x510)] ∧
  Outside StackNat.wT 16 R.rt ∧ Outside W4En.wTy 16 R.rt ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧ slow = 0 ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  NE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  NE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ yl ≤ 2 ^ 9 ∧ yc < 2 ^ 64 ∧
  NE R L sp K st s.mem xp (8 * xc) ∧ s.mem.accessible xp (8 * xc) false = true ∧ xp + 8 * xc ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
  zp < 2 ^ 64 ∧ zl ≤ zc ∧ zc < 2 ^ 40 ∧
  ((0 < zc → (0 < xc ∧ zp + 8 * zc = xp + 8 * xc) ∨ (0 < yc ∧ zp + 8 * zc = yp + 8 * yc) ∨
    ZOK R L g fs sp K st zp zc xp xc yp yl mp n s.mem) ∧ Outside zp (8 * zc) [(sp - K, sp + 0x510)]) ∧
  NE R L sp K st s.mem RunIface.gA 32 ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - K, sp + 0x510), (zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) ∧
    NHyp.StkApart s.mem st op 8) ∧
  0 < st ∧ st < 2 ^ 48 ∧ StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 0x510) ∧ Apart st 24 (g + 16) 8 ∧
  Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 0x510) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  (stCap s.mem st = 0 → stW s.mem st = 0) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (W4En.free s.mem st).1 (W4En.free s.mem st).2 ∧
  Apart (W4En.free s.mem st).1 (W4En.free s.mem st).2 RunIface.gA 32 ∧
  Apart (W4En.free s.mem st).1 (W4En.free s.mem st).2 (fs - 8) 8 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  stLen s.mem st + needR xl n ≤ 2 ^ 16 ∧ stLen s.mem st + needS xl yl n ≤ 2 ^ 16 ∧
  stLen s.mem st + needP xl yl (Nat.log2 (natVal s.mem mp n)) ≤ 2 ^ 16 ∧
  makeCost 1 + max (costR (stLen s.mem st) xl n) (makeCost n + max (costS (stLen s.mem st) xl yl n)
    (costP (stLen s.mem st) xl yl (Nat.log2 (natVal s.mem mp n)))) ≤ b ∧
  ExpOdd.OBud costF n costD xl yl (stLen s.mem st) (b - makeCost n) ∧
  R.inv b L g (view R.rt L s.mem) ∧
  XG s.mem st xp xl xc

theorem NPreS.of_NPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (h : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow s) :
    NPreS R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow s := by
  obtain ⟨⟨-, e1, e2, e3, e4, e5, e6, ⟨c1, c2, -, c4, cR⟩, e8⟩, h2, h3, h4, h5, h6, -, -, -, -, -, -, hR⟩ := h
  exact ⟨⟨e1, e2, e3, e4, e5, e6, ⟨c1, c2, c4, cR⟩, e8⟩, h2, h3, h4, h5, h6, hR⟩

theorem NPre.of_NPreS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (h : NPreS R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (r1 : s.mem.readLE (sp + 0x4a0) 8 = yp) (r2 : s.mem.readLE (sp + 0x4a8) 8 = yl) (r3 : s.mem.readLE (sp + 0x4b0) 8 = yc)
    (r4 : s.mem.readLE (sp + 0x4b8) 8 = mp) (r5 : s.mem.readLE (sp + 0x4c0) 8 = n) (r6 : s.mem.readLE (sp + 0x4c8) 8 = mc)
    (r0 : s.regs 4 = BitVec.ofNat 64 (sp + 0x498)) :
    NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow s := by
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, ⟨c1, c2, c4, cR⟩, e8⟩, h2, h3, h4, h5, h6, hR⟩ := h
  have c3 : sp + 0x510 ≤ 2 ^ 48 := by
    have h48 := Janus.Arm64.Memory.accessible_bound s.mem c4
    rw [← Nat.add_assoc, Nat.sub_add_cancel c2] at h48; exact h48
  exact ⟨⟨r0, e1, e2, e3, e4, e5, e6, ⟨c1, c2, c3, c4, cR⟩, e8⟩, h2, h3, h4, h5, h6, r1, r2, r3, r4, r5, r6, hR⟩

/-- `NPreS`'s window facts give `RSP ≥ 0x498` (`K ≤ sp`, `41640 ≤ K`) -/
theorem NPreS.sp {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (h : NPreS R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow s) :
    41640 ≤ sp := by
  obtain ⟨⟨-, -, -, -, hK, -, ⟨-, hKs, -⟩, -⟩, -⟩ := h
  exact Nat.le_trans hK hKs

end FvModexp.Amd64.ExpN

namespace FvModexp.Amd64.NRow

/-- `nat.rem`'s bridged cost -/
def cR : Nat → Nat → Nat → Nat := RemInst.remC
/-- `nat.expNNSlow`'s bridged cost -/
def cS : Nat → Nat → Nat → Nat → Nat :=
  Q.ExpSlow.slowBr (Q.ExpSlow.costQ sqrCQ mulCQ (Q.NatDiv.costQ Q.drsCQ)) Q.ExpSlow.needH
/-- `nat.expNNPowerOfTwo`'s cost -/
def cP : Nat → Nat → Nat → Nat → Nat := P2D.costP P2W2.costB P2W4.costB

theorem libW_libN : ∀ x, LibW.names.contains x = true → LibN.names.contains x = true := by
  have h : LibW.names.Sublist LibN.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem libRem_libN : ∀ x, LibRem.names.contains x = true → LibN.names.contains x = true := by
  have h : LibRem.names.Sublist LibN.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem libW_nfN : LibW.names.contains ExpN.fn = false := by decide +kernel
theorem libRem_nfN : LibRem.names.contains ExpN.fn = false := by decide +kernel

/-- the stack argument `y` (`RSP + 8 / 16 / 24`), numeral offsets -/
@[reducible] def ArgY (s : State) (y yl yc : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = y ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc

/-- the stack argument `m` (`RSP + 32 / 40 / 48`), numeral offsets -/
@[reducible] def ArgM (s : State) (m n mc : Nat) : Prop :=
  s.mem.readLE ((s.regs 4).toNat + 32) 8 = m ∧ s.mem.readLE ((s.regs 4).toNat + 40) 8 = n ∧
    s.mem.readLE ((s.regs 4).toNat + 48) 8 = mc

/-- the precondition: the stack arguments `y`, `m` (literal `RSP + k` offsets) and `ExpN.Pre` at `K = 41640` with the
closed callee costs, its `NPre` part WITHOUT the stack-argument reads (`ExpN.NPreS`); `toPre`: it implies `ExpN.Pre` -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (costD : Nat)
    (z zl zc st x xl xc y yl yc m n mc slow : Nat) (s : State) : Prop :=
  ArgY s y yl yc ∧ ArgM s m n mc ∧
    ExpN.NPreS R b L 41640 DivInst.divC costD Q.NatRem.need cR ExpSlow.need P2D.needP cS cP (s.regs 14).toNat
      s.fsBase.toNat ((s.regs 4).toNat - 0x498) z zl zc st x xl xc y yl yc m n mc slow s ∧
    (natVal s.mem m n % 2 = 1 ∨ ∃ k, natVal s.mem m n = 2 ^ k) ∧ NHyp.XFacts R L x xl xc

theorem sp_add {e : Nat} (h : 41640 ≤ e - 0x498) (k : Nat) : e - 0x498 + (0x498 + k) = e + k := by omega

/-- the row precondition is `ExpN.Pre` (with the stack arguments) -/
theorem toPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {costD : Nat}
    {z zl zc st x xl xc y yl yc m n mc slow : Nat} {s : State} (h : Pre R b L costD z zl zc st x xl xc y yl yc m n mc slow s) :
    ExpN.Pre R b L 41640 DivInst.divC costD Q.NatRem.need cR ExpSlow.need P2D.needP cS cP z zl zc st x xl xc y yl yc m n
      mc slow s := by
  obtain ⟨⟨y1, y2, y3⟩, ⟨m1, m2, m3⟩, hN, hev, hx⟩ := h
  have e := sp_add hN.sp
  refine ⟨ExpN.NPre.of_NPreS hN ?_ ?_ ?_ ?_ ?_ ?_ ?_, hev, hx⟩
  · rw [e 8]; exact y1
  · rw [e 16]; exact y2
  · rw [e 24]; exact y3
  · rw [e 32]; exact m1
  · rw [e 40]; exact m2
  · rw [e 48]; exact m3
  · rw [show (s.regs 4).toNat - 0x498 + 0x498 = (s.regs 4).toNat by have := e 0; omega]; simp

/-- `ExpN.Pre` with the stack arguments is the row precondition -/
theorem ofPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {costD : Nat}
    {z zl zc st x xl xc y yl yc m n mc slow : Nat} {s : State} (hy : ArgY s y yl yc) (hm : ArgM s m n mc)
    (h : ExpN.Pre R b L 41640 DivInst.divC costD Q.NatRem.need cR ExpSlow.need P2D.needP cS cP z zl zc st x xl xc y yl yc m
      n mc slow s) : Pre R b L costD z zl zc st x xl xc y yl yc m n mc slow s :=
  ⟨hy, hm, ExpN.NPreS.of_NPre h.1, h.2.1, h.2.2⟩

/-- the postcondition (= `ExpN.Post`): `x^y mod m`, normalised, in `z`'s array or a fresh one -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (costD : Nat) (z zc st x xl y yl m n : Nat)
    (s s' : State) : Prop :=
  ExpN.Post R b L 41640 costD cR cS cP z zc st x xl y yl m n s s'

/-- the closed callee shapes of `nat.expNN` (no even path) -/
theorem dhyps (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    ExpN.DHyps impl R 41640 DivInst.divC ExpSlow.need P2D.needP cS cP Q.NatDiv.names 41512 LibW.names 41952
      LibW.names 42520 :=
  have hc : Janus.Contracts.EqHashModel.CodeIn64 (Extracted.program.ofImpl impl) (LibN.program.link impl) := by
    rw [LibN.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibN.names
  { mkN := MakesliceLiveContract64.of_codeIn hc hmk, clr := hmc, mv := hmv, mkO := hmk, gr := hgr, wb := hwb,
    div := DivInst.hyp impl hap R hgr hmc hwb hmk hmv hmz, hnsD := DivInst.ns_sub, hnsW4 := DivInst.ns_w4,
    hnsW2 := DivInst.ns_w2, hKD := by decide,
    slow := Q.ExpSlow.slowCl hap hgr hmc hmv hmz hmk hwb, hnsS := libW_libN, hnfS := libW_nfN, hKS := by decide,
    p2 := P2DRow.hyp impl hap R hgr hmc hmv hmk hno hwb 42520 (by decide) (by decide),
    hnsP := libW_libN, hnfP := libW_nfN, hKP := by decide }

theorem fnN_eq : segAddr Extracted.program ExpN.fn = ExpN.fnN := by decide

theorem bvN (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`** (amd64): `z.expNN(stk, x, y, m, false)` with `stk ≠ nil` and `m` odd or a power of two returns
`x^y mod m` (`Pre` / `Post`), for every runtime meeting the live allocation / copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (costD : Nat) (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc slow : BitVec 64) (y yl yc m n mc : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program ExpN.fn) [z, zl, zc, st, x, xl, xc, slow]
      (Pre R b L costD z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m n mc slow.toNat)
      (Post R b L costD z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m n) := by
  have hS0 := ExpN.ens_noEven impl hap R (dhyps impl hap R hgr hmc hmv hmz hmk hno hwb)
    (RemInst.hyp impl hap R hgr hmc hwb hmk hmv hmz) libRem_libN libRem_nfN (by decide) (costD := costD)
    b L z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m n mc slow.toNat
  simp only [bvN] at hS0
  have h := Ensures.full64 hap (by simp [numIntRegs]) hS0
  intro ret hret s hs hpre
  exact h ret hret s hs (toPre hpre)

end FvModexp.Amd64.NRow

namespace FvModexp.Amd64.NRow.Witness

open Janus.Contracts.Toy FvModexp.Amd64.AsmWit FvModexp.Amd64.EvenHyp FvModexp.Amd64.ExpHyp
open FvModexp.Amd64.P2DRow.Witness (NA OP WW BW gAw wbAw adxW nA_eq gA_eq wbA_eq hret hty)

set_option maxRecDepth 100000

/-- the stack header `{w: OA + 0x200, len: 0, cap: 4}` -/
abbrev ST : Nat := OA + 0x100
abbrev XP : Nat := OB + 0x100
abbrev YP : Nat := OB + 0x200
abbrev MP : Nat := OB + 0x300
abbrev KW : Nat := 41640
/-- the division-cost parameter of the witness -/
abbrev CD : Nat := 30000

/-- `x = [3]`, `y = [5]` (at `SP0 + 8 …`), `m = [7]` (at `SP0 + 32 …`), the stack header, `natOne = {OP, 1, 1}` with
`OP[0] = 1`, the four `math/big` thresholds; all other bytes 0 (the return address `RET` at `SP0` from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = MP then 7 else if a = OP then 1
  else if a = ST + 1 then 0x02 else if a = ST + 2 then 0xD0 else if a = ST + 16 then 4
  else if a = SP0 + 9 then 0x02 else if a = SP0 + 10 then 0xE0 else if a = SP0 + 16 then 1 else if a = SP0 + 24 then 1
  else if a = SP0 + 33 then 0x03 else if a = SP0 + 34 then 0xE0 else if a = SP0 + 40 then 1
  else if a = SP0 + 48 then 1
  else if a = NA + 1 then 0x08 else if a = NA + 2 then 0xE0 else if a = NA + 8 then 1 else if a = NA + 16 then 1
  else if a = gAw then 40 else if a = gAw + 8 then 40 else if a = gAw + 16 then 12 else if a = gAw + 24 then 80 else 0

def regs : List Janus.Arm64.Region :=
  [⟨SP0 - WW, WW + 0x100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨gAw, 32, true⟩, ⟨wbAw, 16, true⟩, ⟨adxW, 8, false⟩, ⟨NA, 24, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP,
    BitVec.ofNat 64 1, BitVec.ofNat 64 1, BitVec.ofNat 64 0]

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 ST else if i = 6 then BitVec.ofNat 64 XP else if i = 8 then 1
      else if i = 9 then 1 else if i = 4 then BitVec.ofNat 64 SP0
      else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program ExpN.fn),
    flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program ExpN.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) : mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv BW [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
      if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

theorem stLen0 : stLen mem0 ST = 0 := by decide +kernel

theorem one0 : NatOne R [] mem0 OP ([(SP0 - 1176 - 41640, SP0 - 1176 + 1296), (0, 0 + 8 * 0)] ++ stWs mem0 ST) ∧
    NHyp.StkApart mem0 ST OP 8 := by
  dsimp only [NatOne]
  rw [nA_eq]
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rw [acc0]; decide +kernel,
    ?_, ?_, by rw [acc0]; decide +kernel, by decide, Or.inr ?_, ?_⟩, fun _ => ⟨?_, fun _ => ?_⟩⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [stWs, stkWs, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [Apart]; decide
  · simp only [Apart]; decide +kernel

set_option maxHeartbeats 64000000 in
/-- the witness state satisfies the precondition (`3^5 mod 7`, `z = nil`, `slow = false`) -/
theorem preE : ArgY s0 YP 1 1 ∧ ArgM s0 MP 1 1 ∧
    ExpN.Pre R BW [] 41640 DivInst.divC CD Q.NatRem.need cR ExpSlow.need P2D.needP cS cP 0 0 0 ST XP 1 1 YP 1 1 MP 1 1 0
      s0 := by
  have hm : s0.mem = mem0 := rfl
  have h4 : (s0.regs 4).toNat = SP0 := by decide
  have h14 : (s0.regs 14).toNat = G0 := by decide
  have hfs : s0.fsBase.toNat = T0 + 8 := by decide
  refine ⟨⟨by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel⟩,
    ⟨by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel, by rw [h4, hm]; decide +kernel⟩, ?_, ?_, ?_⟩
  · unfold ExpN.NPre ExpN.NEnv CallW.CEnv
    rw [h4, h14, hfs, hm]
    repeat' (first
      | exact inv1 _
      | exact WStubs.serves []
      | exact roOut
      | exact dataLoaded _ _
      | apply And.intro)
    all_goals try simp only [stLen0]
    all_goals first
      | decide
      | exact ⟨OP, one0⟩
      | (simp only [NatNorm]; decide +kernel)
      | (intro r hr; simp at hr; done)
      | (intro h; exact absurd h (by decide))
      | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
      | (simp only [Apart, gA_eq, wbA_eq, nA_eq]; decide +kernel)
      | (rw [acc0]; decide +kernel)
      | (simp only [StkOK, NatLive, Held, InRanges, rt_eq, outside_cons, outside_nil, and_true, acc0]; decide +kernel)
      | decide +kernel
      | trivial
      | skip
  · exact Or.inl (by decide +kernel)
  · refine ⟨⟨by decide, by decide, fun _ => ⟨?_, by decide⟩⟩, fun _ => by simp only [gA_eq, Apart]; decide⟩
    simp only [Held, InRanges, rt_eq, outside_cons, outside_nil, and_true]; decide +kernel

/-- the witness state satisfies the row precondition -/
theorem pre : Pre R BW [] CD 0 0 0 ST XP 1 1 YP 1 1 MP 1 1 0 s0 := ofPre preE.1 preE.2.1 preE.2.2

/-- `pre` at the `BitVec` arguments of `correctness` -/
theorem preB : Pre R BW [] CD (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat
    (BitVec.ofNat 64 ST).toNat (BitVec.ofNat 64 XP).toNat (1 : BitVec 64).toNat (1 : BitVec 64).toNat YP 1 1 MP 1 1
    (0 : BitVec 64).toNat s0 := by
  have e0 : (0 : BitVec 64).toNat = 0 := by decide
  have e1 : (BitVec.ofNat 64 ST).toNat = ST := by decide
  have e2 : (BitVec.ofNat 64 XP).toNat = XP := by decide
  have e3 : (1 : BitVec 64).toNat = 1 := by decide
  rw [e0, e1, e2, e3]; exact pre

/-- Every contract hypothesis of the (closed) `correctness` and every conjunct of its precondition hold together: the
shared witness runtime, budget `BW`, division bound `CD`, empty live set, the call `z.expNN(stk, 3, 5, 7, false)` with
`z = nil` and the stack `{w, 0, 4}`; one call-site state per runtime contract. -/
theorem nonvacuous :
    ∃ (impl : List Amd64.Segment) (R : RtInv) (costD : Nat) (b : Nat) (L : List (Nat × Nat))
    (z zl zc st x xl xc slow : BitVec 64) (y yl yc m n mc : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program ExpN.fn)
      [z, zl, zc, st, x, xl, xc, slow] s ∧
    Pre R b L costD z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc m n mc slow.toNat s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      DivRowQ.Witness.mvzSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Post R b L costD z.toNat zc.toNat st.toNat x.toNat xl.toNat y yl m n s s' :=
  ⟨WStubs.impl, R, CD, BW, [], 0, 0, 0, BitVec.ofNat 64 ST, BitVec.ofNat 64 XP, 1, 1, 0, YP, 1, 1, MP, 1, 1, RET, s0,
    WStubs.hap,
    by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _,
    by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R,
    by rw [WStubs.addr_mv]; exact WStubs.mvz R,
    by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _,
    by rw [WStubs.addr_no]; exact WStubs.no [] hty _,
    by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _, hret, setup, preB,
    ⟨[], 0x1000, callS5 WStubs.grA OA 2 1 1 Extracted.dataAddr.«type:big.Word#51b931e8», by rw [WStubs.addr_gr]; rfl,
      by rw [WStubs.addr_gr]; exact site_gr _⟩,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 0, by rw [WStubs.addr_mv]; rfl,
      by rw [WStubs.addr_mv]; exact DivRowQ.Witness.site_mvz _⟩,
    ⟨[], 0x1000, callS WStubs.mkA Extracted.dataAddr.«type:big.Word#51b931e8» 1 1, by rw [WStubs.addr_mk]; rfl,
      by rw [WStubs.addr_mk]; exact site_mk _⟩,
    ⟨[], 0x1000, callS WStubs.noA Extracted.dataAddr.«type:big.Word#51b931e8» 0 0, by rw [WStubs.addr_no]; rfl,
      by rw [WStubs.addr_no]; exact site_no _⟩,
    ⟨[], 0x1000, callS WStubs.wb2A 0 0 0, by rw [WStubs.addr_wb2]; rfl, by rw [WStubs.addr_wb2]; exact site_wb _ _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_gr]; exact WStubs.gr [] hty _)
      (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      (by rw [WStubs.addr_mv]; exact WStubs.mvz R)
      (by rw [WStubs.addr_mk]; exact WStubs.mk [] hty _) (by rw [WStubs.addr_no]; exact WStubs.no [] hty _)
      (by rw [WStubs.addr_wb2]; exact WStubs.wb2 [] hty _) CD BW []
      0 0 0 (BitVec.ofNat 64 ST) (BitVec.ofNat 64 XP) 1 1 0 YP 1 1 MP 1 1 RET hret s0 setup preB⟩

end FvModexp.Amd64.NRow.Witness
