import Janus

/-! The return of a callee summary in the canonical Go ABIInternal shape on amd64 (`Janus.Contracts.retState64`): a final state that
returns to the return address with `RSP + 8`, `RBP`, `R14`, `X15`, the `FS` base, the direction flag, `MXCSR` and the x87 state kept
is a `retState64` (via `Janus.Contracts.retState64_intro`); its memory is the final state's. -/

namespace FvModexp.Ret64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts

theorem ret_intro {s fin : State} {res : List W64} {rs : List (Nat × Nat)} {P : Memory → Prop}
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df)
    (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = res.getD 0 (fin.regs 0)) (h1 : fin.regs 3 = res.getD 1 (fin.regs 3))
    (h2 : fin.regs 1 = res.getD 2 (fin.regs 1))
    (hm : MemFrame s.mem fin.mem rs) (hP : P fin.mem) :
    ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
      fin = retState64 s junk res f x yh m zh kr ∧ MemFrame s.mem m rs ∧ P m :=
  ⟨_, _, _, _, _, _, _, retState64_eq hrip h4 h5 h14 hx hfs hdf hmx h0 h1 h2 hx87 hfw, hm, hP⟩

theorem ret_intro0 {s fin : State} {res : List W64} {rs : List (Nat × Nat)}
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df)
    (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = res.getD 0 (fin.regs 0)) (h1 : fin.regs 3 = res.getD 1 (fin.regs 3))
    (h2 : fin.regs 1 = res.getD 2 (fin.regs 1)) (hm : MemFrame s.mem fin.mem rs) :
    ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
      fin = retState64 s junk res f x yh m zh kr ∧ MemFrame s.mem m rs :=
  ⟨_, _, _, _, _, _, _, retState64_eq hrip h4 h5 h14 hx hfs hdf hmx h0 h1 h2 hx87 hfw, hm⟩

/-- A callee that does not write memory. -/
theorem ret_mem {s fin : State} {res : List W64}
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df)
    (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = res.getD 0 (fin.regs 0)) (h1 : fin.regs 3 = res.getD 1 (fin.regs 3))
    (h2 : fin.regs 1 = res.getD 2 (fin.regs 1)) (hm : fin.mem = s.mem) :
    ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (zh : Nat → BitVec 256) (kr : Nat → W64),
      fin = retState64 s junk res f x yh s.mem zh kr :=
  ⟨_, _, _, _, _, _, hm ▸ retState64_eq hrip h4 h5 h14 hx hfs hdf hmx h0 h1 h2 hx87 hfw⟩

end FvModexp.Ret64
