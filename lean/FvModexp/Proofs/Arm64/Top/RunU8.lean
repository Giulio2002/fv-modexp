import FvModexp.Proofs.Arm64.Conv

set_option autoImplicit false
set_option maxRecDepth 20000

/-! # `Run` (arm64): the `uint8` type descriptor (`.rodata` at `2639168`) read by the `makeslice` call sites

`janus_data` once here (≈ 4 s each) instead of three times in each of RunD1L/RunD2L/RunD2ZA/RunD3ZA (agent top s20). -/

open Janus Janus.Arm64

namespace FvModexp.Arm64.Run

theorem u8T_acc {m : Memory} (hd : Extracted.program.DataLoaded m) : m.accessible 2639168 16 false = true := by
  janus_data hd; exact Memory.accessible_mono _ h_data0 (by omega) (by omega)

theorem u8T_size {m : Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 2639168 8 = 1 := by
  janus_data hd; rw [h_rodata _ _ (by decide)]; decide

theorem u8T_ptr {m : Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 2639176 8 = 0 := by
  janus_data hd; rw [h_rodata _ _ (by decide)]; decide

end FvModexp.Arm64.Run
