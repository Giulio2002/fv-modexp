import FvModexp.Proofs.Amd64.Top.RunDefs

set_option autoImplicit false
set_option maxRecDepth 20000

/-! # `Run` (amd64): the `uint8` type descriptor (`.rodata` at `7231264`) read by the `makeslice` call sites

`janus64_data` once here instead of three times in each of RunC1/RunCP1/RunDM0 (agent top s20), on `u8Prog` (the program
restricted to data segment 0, which holds the descriptor) so it installs ONE segment instead of 49 (asm s84). -/

open Janus Janus.Amd64

namespace FvModexp.Amd64.Run

/-- The `Extracted` program restricted to its data segment 0 (holds the `uint8` descriptor at `7231264`). -/
def u8Prog : Janus.Amd64.Program := { Extracted.program with data := Extracted.program.data.take 1 }

theorem u8Prog_loaded {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : u8Prog.DataLoaded m :=
  fun d h => hd d (List.mem_of_mem_take h)

theorem u8T_acc {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.accessible 7231264 16 false = true := by
  have hd1 := u8Prog_loaded hd; janus64_data hd1; exact Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)

theorem u8T_size {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 7231264 8 = 1 := by
  have hd1 := u8Prog_loaded hd; janus64_data hd1; rw [h_rodata _ _ (by decide)]; decide

theorem u8T_ptr {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : m.readLE 7231272 8 = 0 := by
  have hd1 := u8Prog_loaded hd; janus64_data hd1; rw [h_rodata _ _ (by decide)]; decide

end FvModexp.Amd64.Run
