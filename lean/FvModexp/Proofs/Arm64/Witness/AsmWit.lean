import FvModexp.Proofs.Arm64.Witness.Stubs

/-!
# Witness memory for rows on the Run extraction (arm64; agent asm)

`wmem f rs`: a memory whose bytes are the extraction's read-only data where it lies (`dataSegByte`) and `f a`
elsewhere, with the regions `rs` followed by one read-only region per data object. `dataLoaded` proves
`Extracted.program.DataLoaded (wmem f rs)` for EVERY `f` and `rs` once (Janus `Program.DataLoaded_of_dataSegByte`:
three kernel decisions about the 49 data objects), so a witness never decides `DataLoaded` byte by byte; all the
data lies below `0x500000` (`data_below`), so a witness's own objects above it read `f a` (`wbytes_high`).

`stdRegs`: the regions every asm row witness uses: the stack `[SP0 - 0x2000, SP0 + 0x100)`, the goroutine
`[G0, G0 + 0x100)` (read-only), two object areas `[OA, OA + 0x1000)` (writable) and `[OB, OB + 0x1000)` (writable),
the toy runtime's bump cell + write-barrier buffer and its heap (`Janus.Contracts.Toy`).
-/

namespace FvModexp.Arm64.AsmWit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

set_option maxRecDepth 100000

theorem data_disj : DataSegsDisjoint Extracted.program.data := by unfold DataSegsDisjoint; decide +kernel

theorem data_lt : ∀ d ∈ Extracted.program.data, ∀ b ∈ d.bytes, b < 256 := by decide +kernel

theorem data_below : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0x500000 := by decide +kernel

/-- the witness bytes: the read-only data, else `f` -/
def wbytes (f : Nat → Byte) (a : Nat) : Byte :=
  match dataSegByte Extracted.program.data a with
  | some n => BitVec.ofNat 8 n
  | none => f a

def dataRegs : List Region := Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩

def wmem (f : Nat → Byte) (rs : List Region) : Memory := ⟨wbytes f, rs ++ dataRegs⟩

theorem dataSegByte_high {a : Nat} (h : 0x500000 ≤ a) : dataSegByte Extracted.program.data a = none := by
  unfold dataSegByte
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have := data_below d hd
  split
  · rename_i hc; omega
  · rfl

theorem wbytes_high (f : Nat → Byte) {a : Nat} (h : 0x500000 ≤ a) : wbytes f a = f a := by
  unfold wbytes; rw [dataSegByte_high h]

theorem dataLoaded (f : Nat → Byte) (rs : List Region) : Extracted.program.DataLoaded (wmem f rs) := by
  refine Program.DataLoaded_of_dataSegByte data_disj (fun d hd => ?_) data_lt fun a n h => ?_
  · have hb := data_below d hd
    refine List.any_eq_true.2 ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_right _ (List.mem_map_of_mem hd), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_false, Bool.and_true]
    exact ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, Nat.le_trans hb (by decide)⟩
  · show (wbytes f a).toNat = n % 256
    unfold wbytes; rw [h]; simp

/-! ## The standard layout of an asm row witness -/

def SP0 : Nat := 0x800000
def G0 : Nat := 0x900000
def OA : Nat := 0xA00000
def OB : Nat := 0xB00000
def RET : Nat := 0x1000

def stdRegs : List Region :=
  [⟨SP0 - 0x2000, 0x2100, true⟩, ⟨G0, 0x100, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩]

/-- `f` for the toy runtime: the bump cell holds `HEAP` (byte 3 = `0x10`), everything else is given by `g`. -/
def toyBytes (g : Nat → Byte) (a : Nat) : Byte := if a = BUMP + 3 then 0x10 else if a < HEAP then g a else 0

/-- the standard runtime of a witness: the toy allocator serving every request -/
abbrev R : RtInv := toyR [] fun _ _ => True

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

/-- accessibility does not depend on the bytes -/
theorem acc_eq (g : Nat → Byte) {rs : List Region} (a n : Nat) (w : Bool) :
    (wmem g rs).accessible a n w = (wmem (fun _ => 0) rs).accessible a n w :=
  Memory.accessible_congr rfl a n w

/-- the toy runtime's invariant for a witness memory (the bump cell's value is checked per witness, by `decide`) -/
theorem inv0 (g : Nat → Byte) (hbump : (wmem (toyBytes g) stdRegs).readLE BUMP 8 = HEAP) (gp : Nat) :
    R.inv 0x1000 [] gp (view R.rt [] (wmem (toyBytes g) stdRegs)) := by
  refine toyInv_init_live (m := wmem (toyBytes g) stdRegs) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) hbump (fun i hi hi' => ?_) (by rw [acc_eq (toyBytes g)]; decide +kernel)
    (by rw [acc_eq (toyBytes g)]; decide +kernel) (by rw [acc_eq (toyBytes g)]; decide +kernel)
  · show wbytes (toyBytes g) i = 0
    rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
    unfold toyBytes
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by omega)]

end FvModexp.Arm64.AsmWit
