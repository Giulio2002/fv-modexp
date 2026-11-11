import Extracted
import FvModexp.Proofs.Arm64.RequiredGas.Pre

/-! The join-point statements of the `RequiredGas` (arm64) main body as named `Prop`s: each segment lemma (Blk2, Blk3, Fin1, Fin)
assumes the statement of the next segment and proves its own, so that the four modules only import this one and elaborate in
parallel; `RequiredGas.lean` chains them. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The statement of `rg_blk2` under a side condition `P len cap` (named `Prop`s, so that the segment modules compile independently). -/
def Blk2If (P : BitVec 64 → BitVec 64 → Prop) : Prop :=
  ∀ (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0xc4)))
    (hsp : S.sp = s.sp - 416#64) (h0 : S.regs 0 = s.sp - 88#64) (h4 : S.regs 4 = s.sp - 152#64) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE (s.sp.toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE (s.sp.toNat + 32) 8 = cap.toNat)
    (m_x5 : S.mem.readLE (s.sp.toNat - 288) 8 = if len.toNat < 32 then len.toNat else 32)
    (w0 : val256 S.mem (s.sp.toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0) (hP : P len cap),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

abbrev Blk2Stmt : Prop := Blk2If (fun _ _ => True)

/-- The statement of `rg_blk3` under a side condition `P len cap`. -/
def Blk3If (P : BitVec 64 → BitVec 64 → Prop) : Prop :=
  ∀ (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x160)))
    (hsp : S.sp = s.sp - 416#64) (h0 : S.regs 0 = s.sp - 152#64) (h4 : S.regs 4 = s.sp - 216#64) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE (s.sp.toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE (s.sp.toNat + 32) 8 = cap.toNat)
    (m_z0 : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 88)
    (w0 : val256 S.mem (s.sp.toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0)
    (w1 : val256 S.mem (s.sp.toNat - 152) = Calldata.word s.mem ptr.toNat len.toNat 32) (hP : P len cap),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

abbrev Blk3Stmt : Prop := Blk3If (fun _ _ => True)

/-- The statement of `rg_fin1` (a named `Prop`, so that the segment modules compile independently). -/
def Fin1Stmt : Prop :=
  ∀ (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x204)))
    (hsp : S.sp = s.sp - 416#64) (h0 : S.regs 0 = s.sp - 216#64) (h4 : S.regs 4 = BitVec.ofNat 64 (s.sp.toNat - 88)) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE (s.sp.toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE (s.sp.toNat + 32) 8 = cap.toNat)
    (m_z0 : S.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 88) (m_z1 : S.mem.readLE (s.sp.toNat - 24) 8 = s.sp.toNat - 152)
    (w0 : val256 S.mem (s.sp.toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0)
    (w1 : val256 S.mem (s.sp.toNat - 152) = Calldata.word s.mem ptr.toNat len.toNat 32)
    (w2 : val256 S.mem (s.sp.toNat - 216) = Calldata.word s.mem ptr.toNat len.toNat 64),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

/-- The statement of `rg_fin2` under a side condition `P len cap B E` (the cases of `FinA`..`FinE`). -/
def Fin2If (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop) : Prop :=
  ∀ (c ptr len cap B E M : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.pc = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x260)))
    (hsp : S.sp = s.sp - 416#64) (h0 : S.regs 0 = B) (h1 : S.regs 1 = E) (h2 : S.regs 2 = M)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 424#64)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - 504, s.sp.toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.sp.toNat - 416) 8 = ret) (m_fp : S.mem.readLE (s.sp.toNat - 424) 8 = (s.regs 29).toNat)
    (m_c : S.mem.readLE (s.sp.toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE (s.sp.toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE (s.sp.toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE (s.sp.toNat + 32) 8 = cap.toNat)
    (hB : B.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 0))
    (hE : E.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 32))
    (hM : M.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 64)) (hP : P len cap B E),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

/-- The statement of `rg_fin2` (a named `Prop`, so that the segment modules compile independently). -/
abbrev Fin2Stmt : Prop := Fin2If (fun _ _ _ _ => True)

/-- The first two case conditions of `rg_fin2` (the exponent-head slice bounds `getData(input, 96 + B, E)`). -/
abbrev finK1 (len B E : BitVec 64) : Prop := len.toNat - 96 < E.toNat + B.toNat
abbrev finK2 (cap B : BitVec 64) : Prop := B.toNat < cap.toNat - 96
abbrev finK3 (len B : BitVec 64) : Prop := len.toNat - 96 < B.toNat + 32

end FvModexp.Arm64.RG
