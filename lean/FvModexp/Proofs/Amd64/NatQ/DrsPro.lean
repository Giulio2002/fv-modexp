import FvModexp.Proofs.Amd64.NatQ.DrsNorm

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the prologue (natdiv.go:750) up to the head of `u.norm()`

Code `0x5ef880 … 0x5ef8bd`: stack check (`LEAQ -0x108(SP), R12; CMPQ R12, 16(R14); JBE morestack`), `PUSHQ BP;
MOVQ SP, BP; SUBQ $0x180, SP` (`SP' = r - 392`, `r` = entry `RSP`), spills `RAX → r + 32`, `RSI → r + 64`, the defer
record pointer `r - 16` zeroed (`MOVQ X15`), the defer bit (byte `r - 297`) cleared, `JMP` to `u.norm()`'s head.
All frame writes stay in `fw s = win s 400 96`. Twin of Arm64/Nat/DrsPro.lean.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

/-- the frame ranges written by `divRecursiveStep` itself -/
@[reducible] def fw (s : State) : List (Nat × Nat) := win s 400 96

theorem mf_trans {m₀ m₁ m₂ : Memory} {rs : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs) (h₂ : MemFrame m₁ m₂ rs) :
    MemFrame m₀ m₂ rs :=
  ⟨fun a k ho => by rw [h₂.readLE a k ho, h₁.readLE a k ho],
   fun a n w => by rw [h₂.accessible, h₁.accessible]⟩

/-- the frame facts at every point after the prologue (entry state `s`, current state `S`) -/
structure Fr (s S : State) : Prop where
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  reg : S.mem.regions = s.mem.regions
  fr : MemFrame s.mem S.mem (fw s)
  ra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → the head of `u.norm()`: registers `RAX … R10` kept, `z.ptr`, `u.ptr` spilled, defer slots cleared -/
theorem pro0 {R : RtInv} {L : List (Nat × Nat)} (impl : List Amd64.Segment) (s : State) (W : Nat) (r : Nat)
    (hpc : s.rip = BitVec.ofNat 64 0x5ef880) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hce : CallEnv R L s W 96) (hW : 400 ≤ W) (Q : State → Prop)
    (k : ∀ P, P.rip = BitVec.ofNat 64 nHead1 → Fr s P → P.xmm 15 = 0#128 →
      (∀ j, j ≠ 4 → j ≠ 5 → j ≠ 12 → P.regs j = s.regs j) →
      P.mem.readLE ((s.regs 4).toNat + 32) 8 = (s.regs 0).toNat →
      P.mem.readLE ((s.regs 4).toNat + 64) 8 = (s.regs 6).toNat →
      P.mem.readLE ((s.regs 4).toNat - 16) 8 = 0 → P.mem.readLE ((s.regs 4).toNat - 297) 1 = 0 →
      ReachesRet (LibDrs.program.link impl) r P Q) :
    ReachesRet (LibDrs.program.link impl) r s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  clear hLs hout hgr
  janus64_run until [nHead1]
  refine k _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?qR, ?qF, ?_, ?_⟩ ?_ ?qS ?_ ?_ ?_ ?_
  case qF => unfold fw win; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  case qS => intro j h4 h5 h12; simp only [Janus.Amd64.Tactic.setRegF_apply, h4, h5, h12, ite_false]
  all_goals try (janus64_simp; done)
  all_goals (janus64_simp; try omega)

end FvModexp.Amd64.Q.DivRec
