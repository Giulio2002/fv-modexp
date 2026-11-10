import Janus

/-!
# Loop-state bookkeeping for the assembly-kernel summaries (the only metaprogramming of the asm proofs)

`SameA s S` (arm64) / `Same64 s S` (amd64): the loop state `S` agrees with the entry state `s` on everything an ABI0
return must keep (`Ret0`: arm64 `SP`, `R18`, `g`, `FP`, `LR`, the constant system registers; amd64 `RSP`, `RBP`, the
`FS` base, `DF`, `MXCSR`, the x87 state). `same_tac h` / `same64_tac h` close `SameA s S'` / `Same64 s S'` for the state
`S'` a run reaches from a `h : SameA s S` state without writing those registers. Pure tactic macros: nothing is trusted.
-/

namespace FvModexp.Asm

/-- arm64: the loop state `S` keeps what an ABI0 return from `s` must keep -/
structure SameA (s S : Janus.Arm64.State) : Prop where
  sp : S.sp = s.sp
  r18 : S.regs 18 = s.regs 18
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.regs 29
  r30 : S.regs 30 = s.regs 30
  fpcr : S.fpcr = s.fpcr
  tpidr : S.tpidr = s.tpidr
  dczid : S.dczid = s.dczid
  excl : S.excl = s.excl
  exclPass : S.exclPass = s.exclPass

theorem SameA.refl (s : Janus.Arm64.State) : SameA s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- amd64: the loop state `S` keeps what an ABI0 return from `s` must keep -/
structure Same64 (s S : Janus.Amd64.State) : Prop where
  r4 : S.regs 4 = s.regs 4
  r5 : S.regs 5 = s.regs 5
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  mx : S.mxcsr = s.mxcsr
  x87 : S.x87 = s.x87
  fw : S.fpucw = s.fpucw

theorem Same64.refl (s : Janus.Amd64.State) : Same64 s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- closes `SameA s S'` from `h : SameA s S` -/
macro "same_tac " h:ident : tactic => `(tactic| (
  obtain ⟨hsp, h18, h28, h29, h30, hfp, htp, hdc, hex, hep⟩ := $h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | rfl | exact hsp
  · janus_simp
  · janus_simp
  · janus_simp
  · janus_simp
  · first | rfl | exact hfp
  · first | rfl | exact htp
  · first | rfl | exact hdc
  · first | rfl | exact hex
  · first | rfl | exact hep))

/-- closes `Same64 s S'` from `h : Same64 s S` -/
macro "same64_tac " h:ident : tactic => `(tactic| (
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := $h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | exact h4
  · simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; first | done | exact h5
  · first | rfl | exact hfs
  · first | rfl | exact hdf
  · first | rfl | exact hmx
  · first | rfl | exact h87
  · first | rfl | exact hfw))

end FvModexp.Asm
