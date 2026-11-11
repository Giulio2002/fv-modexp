import Janus

/-! The return of a callee summary in the canonical Go ABIInternal shape (`Janus.Contracts.retStateX`, arm64): a final state that keeps
`SP`, `X18`, `X28`, `X29` and the system registers, with `pc = X30`, is a `retStateX`; its memory is the final state's. -/

namespace FvModexp.Ret

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts

theorem retX_intro {s fin : State} {res : List W64} {rs : List (Nat × Nat)} {P : Memory → Prop}
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (hres : ∀ i, i < res.length → fin.regs i = res.getD i 0)
    (hm : MemFrame s.mem fin.mem rs) (hP : P fin.mem) :
    ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      fin = retStateX s junk res f v m ex ep ∧ MemFrame s.mem m rs ∧ P m :=
  ⟨_, _, _, _, _, _, retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs hres, hm, hP⟩

theorem retX_intro0 {s fin : State} {res : List W64} {rs : List (Nat × Nat)}
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (hres : ∀ i, i < res.length → fin.regs i = res.getD i 0)
    (hm : MemFrame s.mem fin.mem rs) :
    ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      fin = retStateX s junk res f v m ex ep ∧ MemFrame s.mem m rs :=
  ⟨_, _, _, _, _, _, retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs hres, hm⟩

/-- A callee that does not write memory. -/
theorem retX_mem {s fin : State} {res : List W64}
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (hres : ∀ i, i < res.length → fin.regs i = res.getD i 0) (hm : fin.mem = s.mem) :
    ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      fin = retStateX s junk res f v s.mem ex ep :=
  ⟨_, _, _, _, _, hm ▸ retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs hres⟩

theorem rr_mono {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop} (h : ReachesRet p ret s Q)
    (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h
  exact ⟨k, s', h1, h2, hQ _ h3⟩

end FvModexp.Ret
