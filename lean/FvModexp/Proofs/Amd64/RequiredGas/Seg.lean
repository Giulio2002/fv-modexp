import Extracted
import FvModexp.Proofs.Amd64.RequiredGas.Pre

/-! The join-point statements of the `RequiredGas` (amd64) main body as named `Prop`s: each segment lemma (Blk2, Blk3, Fin1, Fin)
assumes the statement of the next segment and proves its own, so that the segment modules only import this one and elaborate in
parallel; `RequiredGas.lean` chains them. The frame: `RSP` at entry is `s.regs 4`; the body runs with `RSP = s.regs 4 - 400`
(`PUSH RBP` + `SUB $0x188`); the input slice and the receiver are spilled to `[RSP + 8, RSP + 40)` of the entry `RSP`. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- The statement of `rg_blk2` (from `+0xf4`, after the first `SetBytes`) under a side condition `P len cap`. -/
def Blk2If (P : BitVec 64 → BitVec 64 → Prop) : Prop :=
  ∀ (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.rip = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0xf4)))
    (h4 : S.regs 4 = s.regs 4 - 400#64) (h14 : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - 496, (s.regs 4).toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.regs 4).toNat 8 = ret) (m_fp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m_c : S.mem.readLE ((s.regs 4).toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE ((s.regs 4).toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE ((s.regs 4).toNat + 32) 8 = cap.toNat)
    (h0 : S.regs 0 = s.regs 4 - 88#64) (h2 : S.regs 2 = s.regs 4 - 152#64)
    (m_x5 : S.mem.readLE ((s.regs 4).toNat - 288) 8 = if len.toNat < 32 then len.toNat else 32)
    (w0 : val256 S.mem ((s.regs 4).toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0) (hP : P len cap),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

abbrev Blk2Stmt : Prop := Blk2If (fun _ _ => True)

/-- The statement of `rg_blk3` (from `+0x1d0`, after the second `SetBytes`) under a side condition `P len cap`. -/
def Blk3If (P : BitVec 64 → BitVec 64 → Prop) : Prop :=
  ∀ (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.rip = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x1d0)))
    (h4 : S.regs 4 = s.regs 4 - 400#64) (h14 : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - 496, (s.regs 4).toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.regs 4).toNat 8 = ret) (m_fp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m_c : S.mem.readLE ((s.regs 4).toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE ((s.regs 4).toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE ((s.regs 4).toNat + 32) 8 = cap.toNat)
    (h0 : S.regs 0 = s.regs 4 - 152#64) (h2 : S.regs 2 = s.regs 4 - 216#64) (m_z0 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 88)
    (w0 : val256 S.mem ((s.regs 4).toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0)
    (w1 : val256 S.mem ((s.regs 4).toNat - 152) = Calldata.word s.mem ptr.toNat len.toNat 32) (hP : P len cap),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

abbrev Blk3Stmt : Prop := Blk3If (fun _ _ => True)

/-- The statement of `rg_fin1` (from `+0x2c2`, after the third `SetBytes`). -/
def Fin1Stmt : Prop :=
  ∀ (c ptr len cap : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.rip = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x2c2)))
    (h4 : S.regs 4 = s.regs 4 - 400#64) (h14 : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - 496, (s.regs 4).toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.regs 4).toNat 8 = ret) (m_fp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m_c : S.mem.readLE ((s.regs 4).toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE ((s.regs 4).toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE ((s.regs 4).toNat + 32) 8 = cap.toNat)
    (h0 : S.regs 0 = s.regs 4 - 216#64) (h2 : S.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 88))
    (m_z0 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 88)
    (m_z1 : S.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat - 152)
    (w0 : val256 S.mem ((s.regs 4).toNat - 88) = Calldata.word s.mem ptr.toNat len.toNat 0)
    (w1 : val256 S.mem ((s.regs 4).toNat - 152) = Calldata.word s.mem ptr.toNat len.toNat 32)
    (w2 : val256 S.mem ((s.regs 4).toNat - 216) = Calldata.word s.mem ptr.toNat len.toNat 64),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

/-- The statement of `rg_fin2` (from `+0x324`: the saturated lengths `B`, `E`, `M` in `RAX`, `RBX`, `RCX`) under a side condition
`P len B E`. -/
def Fin2If (P : BitVec 64 → BitVec 64 → BitVec 64 → Prop) : Prop :=
  ∀ (c ptr len cap B E M : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s S : State)
    (hpre : RgPre c ptr len cap s)
    (hpc : S.rip = BitVec.ofNat 64 (janus_eval% (segAddr Extracted.program "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas" + 0x324)))
    (h4 : S.regs 4 = s.regs 4 - 400#64) (h14 : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - 496, (s.regs 4).toNat + 40)]) (hdl : Extracted.program.DataLoaded S.mem)
    (m_ret : S.mem.readLE (s.regs 4).toNat 8 = ret) (m_fp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m_c : S.mem.readLE ((s.regs 4).toNat + 8) 8 = c.toNat) (m_ptr : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ptr.toNat)
    (m_len : S.mem.readLE ((s.regs 4).toNat + 24) 8 = len.toNat) (m_cap : S.mem.readLE ((s.regs 4).toNat + 32) 8 = cap.toNat)
    (h0 : S.regs 0 = B) (h3 : S.regs 3 = E) (h1 : S.regs 1 = M)
    (hB : B.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 0))
    (hE : E.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 32))
    (hM : M.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 64)) (hP : P len B E),
    Returns (Extracted.program.withExit ret) S (fun s' => ABIReturn s s' ∧ RgPost ptr len s s')

abbrev Fin2Stmt : Prop := Fin2If (fun _ _ _ => True)

/-- The case conditions of `rg_fin2`: the exponent head is skipped (`len(input[96:]) ≤ baseLen`), `expLen > 32`, and the slice
`input[96:][baseLen : baseLen + 32]` resp. `[baseLen : baseLen + expLen]` is cut short by the end of the input. -/
abbrev finS (len B : BitVec 64) : Prop := len.toNat - 96 ≤ B.toNat
abbrev finE (E : BitVec 64) : Prop := 32 < E.toNat
abbrev finN1 (len B : BitVec 64) : Prop := len.toNat - 96 < B.toNat + 32
abbrev finN2 (len B E : BitVec 64) : Prop := len.toNat - 96 < B.toNat + E.toNat

end FvModexp.Amd64.RG
