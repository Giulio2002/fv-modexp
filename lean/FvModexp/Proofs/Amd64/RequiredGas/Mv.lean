import Extracted
import FvModexp.Proofs.Common.Bytes
import FvModexp.Proofs.Amd64.RequiredGas.Defs

/-! `runtime.memmove(dst, src, n)` for `n ≤ 32` (amd64), run from its extracted code: one symbolic run per length (the paths for
`n ≤ 32` use 1/2/4/8-byte moves and two `MOVOU`s, never `runtime.memmoveBits`). -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- A byte register write (`MOVB`) merged into a zero register. -/
theorem merge8 (x : Nat) : (0#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 x)).toNat % 256 = x % 256 := by simp

/-- A 16-bit register write (`MOVW`) merged into the old register value. -/
theorem merge16 (a : BitVec 64) (x : Nat) :
    (a &&& 18446744073709486080#64 ||| BitVec.setWidth 64 (BitVec.ofNat 16 x)).toNat % 65536 = x % 65536 := by
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (65536 : Nat) = 2 ^ 16 from rfl, Nat.or_mod_two_pow, Nat.and_mod_two_pow]
  simp

theorem rdmod (m : Memory) (a k n : Nat) (h : 256 ^ k ≤ n) : m.readLE a k % n = m.readLE a k :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt m a k) h)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem mv : Summary Extracted.program mvA (fun s => MvPre (s.regs 1).toNat s ∧ (s.regs 1).toNat ≤ 32)
    (fun s s' => MvPost (s.regs 1).toNat s s') := by
  intro s hpc ⟨⟨⟨hra, hra2, hra3⟩, _hl0, hd48, hs48, hdw, hsr, hdj, hdr, hdl⟩, hn⟩
  simp only [Janus.Spec.Disjoint] at hdj hdr
  generalize hk : (s.regs 1).toNat = k at *
  have hlt : k < 33 := by omega
  have hl' : s.regs 1 = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by simp [hk]; omega)
  janus_cases hlt
  all_goals
    janus64_run
    all_goals first
      | (exfalso; omega)
      | (refine Ret64.ret_intro rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by janus_frame) ⟨?_, ?_⟩
         · intro i hi
           dsimp only
           try simp only [Janus.Arm64.Memory.bytes_writeLE]
           repeat' split
           all_goals first
             | (exfalso; omega)
             | ((try simp only [merge8, merge16]); (try simp (disch := decide) only [rdmod])
                rw [Bytes.byte_readLE_at _ _ _ _ _ (by omega) (by omega)]; congr 1; omega)
         · dl_close)

end FvModexp.Amd64.RG
