/-! check-ra-pin self-test (amd64): the probe forms of /srv/janus-ops/v033/probe/RspBypass64.lean (each must be FLAGGED)
and controls (must be CLEAN). Statements only (proofs `sorry`: never imported by the release tree). Expected verdicts:
the `-- expect:` comment on each theorem; checked by scripts/check-ra-pin --selftest. -/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Spec Janus.Contracts

namespace RaPinProbe64

-- expect: FLAG
theorem c1 : Ensures Extracted.program Extracted.entry []
    (fun s => (∃ sp, (s.regs 4).toNat = sp ∧ s.mem.readLE sp 8 = 0)) (fun _ _ => True) := sorry
-- expect: FLAG
theorem c2 : Ensures Extracted.program Extracted.entry []
    (fun s => (∃ sp, (s.regs 4).toNat ≤ sp ∧ sp ≤ (s.regs 4).toNat ∧ s.mem.readLE sp 8 = 0)) (fun _ _ => True) := sorry
def RdZero (m : Janus.Arm64.Memory) (a : Nat) : Prop := m.readLE a 8 = 0
-- expect: FLAG
theorem c3 : Ensures Extracted.program Extracted.entry []
    (fun s => RdZero s.mem (s.regs 4).toNat) (fun _ _ => True) := sorry
-- expect: FLAG
theorem c4 : Ensures Extracted.program Extracted.entry []
    (fun s => (∀ i, i < 8 → s.mem.bytes ((s.regs 4).toNat + i) = 0)) (fun _ _ => True) := sorry
-- expect: FLAG
theorem c5 : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 4).toNat = 0x100000 ∧ s.mem.readLE 0x100000 8 = 0) (fun _ _ => True) := sorry
-- expect: FLAG
theorem c6 : Ensures Extracted.program Extracted.entry []
    (fun s => (∀ sp, sp = (s.regs 4).toNat → s.mem.readLE sp 8 = 0)) (fun _ _ => True) := sorry
-- expect: FLAG
theorem c7 : Ensures Extracted.program Extracted.entry []
    (fun s => (let a := (s.regs 4).toNat; s.mem.readLE a 8 = 0)) (fun _ _ => True) := sorry
def zeroMem (m : Janus.Arm64.Memory) : Janus.Arm64.Memory := { m with bytes := fun _ => 0 }
-- expect: FLAG
theorem c8 : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem = zeroMem s.mem) (fun _ _ => True) := sorry
-- expect: FLAG
theorem d0 : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0) (fun _ _ => True) := sorry
-- expect: FLAG  (alias through a theorem binder)
theorem t1 (sp : Nat) : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 4).toNat = sp ∧ s.mem.readLE sp 8 < 2 ^ 20) (fun _ _ => True) := sorry
-- expect: FLAG  (EnsuresWithin form; two-sided closed bounds + constant read)
theorem t2 : EnsuresWithin (fun _ => 100) Extracted.program Extracted.entry []
    (fun s => 0x1000 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat ≤ 0x1000 ∧ s.mem.readLE 0x1000 8 = 0) (fun _ _ => True) := sorry
-- expect: FLAG  (RSP + k, symbolic k)
theorem t3 (k : Nat) : Ensures Extracted.program Extracted.entry []
    (fun s => k < 8 ∧ s.mem.readLE ((s.regs 4).toNat + k) 8 = 0) (fun _ _ => True) := sorry
-- expect: CLEAN  (stack argument at RSP + 8, window bounds)
theorem ok1 (vp : Nat) : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem.readLE ((s.regs 4).toNat + 8) 8 = vp ∧ (s.regs 4).toNat % 8 = 0 ∧
      Outside vp 8 [((s.regs 4).toNat - 64, (s.regs 4).toNat + 16)] ∧ s.mem.readLE vp 8 = 3) (fun _ _ => True) := sorry
-- expect: CLEAN  (one-sided closed bound on RSP, constant data read)
theorem ok2 : Ensures Extracted.program Extracted.entry []
    (fun s => 4096 ≤ (s.regs 4).toNat ∧ s.mem.readLE 0x1000 8 = 0) (fun _ _ => True) := sorry

end RaPinProbe64
