import FvModexp.Proofs.Amd64.Exp.W4Defs
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# window-4 (amd64): a `nat.montgomery` call in continuation form (agent expmc s42)

`montCall`: at the callee entry (after the caller's `CALL`, `RSP = r`, return address `ra` on the stack) with the
static facts `MontW.MCall` and the dynamic ones `MontW.MDyn`, the call returns to `ra` with `MontW.MPost`. Proved once,
used by every call of the loop (SPEED LESSONS: stop at the callee entry, prove its pre in a small lemma).
`ra_of`: return addresses inside window-4's own segment (`seg34`, base `0x5eb060`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Loop

theorem fnE_eq : fnE = 6205536 := by decide

set_option maxRecDepth 20000 in
/-- a return address inside window-4's segment is a return address of every callee program without window-4 -/
theorem ra_of {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x1300) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (6205536 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg34) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by simpa using hn) i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5eb060 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg34] using this

theorem mont_not : LibMont.names.contains fn = false := by decide

set_option maxRecDepth 20000 in
/-- **a montgomery call** (callee `RSP = r`, entry of `nat.montgomery` in `LibW`), continuation form -/
theorem montCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g gv fs r n mp mc rp rc xp yp k : Nat} {zl xc yc : BitVec 64}
    {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hc : MontW.MCall R L g gv fs r n mp mc rp rc xp yp) (hk : k < 2 ^ 64)
    (hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr LibW.program MontHyp.fn)) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 rp) (h3 : S.regs 3 = zl) (h1 : S.regs 1 = BitVec.ofNat 64 rc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 n) (h8 : S.regs 8 = xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false) (hd : MontW.MDyn R b L g gv fs r n mp mc rp rc xp yp k S)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 ra → MontW.MPost R b L g r n mp rp rc xp yp k S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := MontW.sum impl hap R hclr hmv b L g gv fs r n mp mc rp rc xp yp k zl xc yc hc hk
  refine ReachesRet.call_regions hS hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hd⟩
    fun s' hr hq hrg => K s' (by rw [hr, retAddrOf_eq, hrd]) hq hrg
  simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]

end FvModexp.Amd64.W4Loop
