import FvModexp.Proofs.Amd64.Top.RunDefs

set_option autoImplicit false
set_option maxRecDepth 20000

/-! # `Run` (amd64): the `uint8` type descriptor (`.rodata` at `7231264`) read by the `makeslice` call sites

`janus64_data` once here instead of three times in each of RunC1/RunCP1/RunDM0 (agent top s20). -/

open Janus Janus.Amd64

namespace FvModexp.Amd64.Run

theorem u8T_acc {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.accessible 7231264 16 false = true := by
  janus64_data hd; exact Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)

theorem u8T_size {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 7231264 8 = 1 := by
  janus64_data hd; rw [h_rodata _ _ (by decide)]; decide

theorem u8T_ptr {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 7231272 8 = 0 := by
  janus64_data hd; rw [h_rodata _ _ (by decide)]; decide

end FvModexp.Amd64.Run
