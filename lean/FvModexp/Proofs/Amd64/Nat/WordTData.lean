import Extracted

set_option autoImplicit false

/-!
# The `big.Word` type descriptor (amd64): readable, size word `8`, pointer-data word `0`

The facts `makeslice(Word, …)` call sites need, proved ONCE here: `janus64_data` on the Run extraction costs ≈ 36 s per
use (it evaluates every data segment), so the nat.add / nat.sub / mulAddWW allocation paths take this lemma instead
(divmc s32; same statement as `FvModexp.Amd64.SetBytes.wordT_data`, agent top s18).
-/

open Janus Janus.Amd64 Janus.Amd64.Tactic

namespace FvModexp.Amd64

set_option maxRecDepth 20000 in
theorem wordT_data {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.accessible 7233184 16 false = true ∧ m.readLE 7233184 8 = 8 ∧ m.readLE 7233192 8 = 0 := by
  janus64_data hd
  exact ⟨Janus.Arm64.Memory.accessible_mono _ h_data1 (by omega) (by omega), by rw [h_rodata _ _ (by decide)]; decide,
    by rw [h_rodata _ _ (by decide)]; decide⟩

end FvModexp.Amd64
