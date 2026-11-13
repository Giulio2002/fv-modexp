/-! check-ra-pin self-test (arm64): the probe forms of /srv/janus-ops/v033/probe/LrPin.lean (FLAG) and a control. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Spec Janus.Contracts

namespace RaPinProbeArm

-- expect: FLAG
theorem e1 : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 30).toNat = 0) (fun _ _ => True) := sorry
-- expect: FLAG
theorem e2 : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 30).toNat < 2 ^ 20) (fun _ _ => True) := sorry
-- expect: FLAG  (regLR spelling)
theorem e3 : Ensures Extracted.program Extracted.entry []
    (fun s => s.regs regLR = 0) (fun _ _ => True) := sorry
def LrLow (s : Janus.Arm64.State) : Prop := (s.regs 30).toNat < 2 ^ 40
-- expect: FLAG  (through a project definition)
theorem e4 (n : Nat) : Ensures Extracted.program Extracted.entry []
    (fun s => n < 5 ∧ LrLow s) (fun _ _ => True) := sorry
-- expect: FLAG  (memory equation)
theorem e5 (m : Memory) : Ensures Extracted.program Extracted.entry []
    (fun s => s.mem = m) (fun _ _ => True) := sorry
-- expect: CLEAN
theorem ok1 (xp : Nat) : Ensures Extracted.program Extracted.entry []
    (fun s => (s.regs 0).toNat = xp ∧ s.mem.readLE (s.sp.toNat + 8) 8 = 1) (fun _ _ => True) := sorry

end RaPinProbeArm
