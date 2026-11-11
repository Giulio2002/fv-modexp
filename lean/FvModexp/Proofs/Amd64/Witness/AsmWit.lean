import Extracted
import FvModexp.Proofs.Amd64.Conv

/-!
# Witness memory for rows on the Run extraction (amd64; agent asm)

The amd64 twin of `FvModexp.Arm64.AsmWit`: `wmem f rs` reads the extraction's read-only data where it lies and `f`
elsewhere; `dataLoaded` proves `DataLoaded` once for every `f`, `rs` (all amd64 data lies below `0xA00000`).
Layout: stack `[SP0 - 0x2000, SP0 + 0x100)`, goroutine `[G0, G0 + 0x100)`, TLS slot `[T0, T0 + 8)` holding `G0`
(`fsBase = T0 + 8`), object areas `OA`, `OB`, the toy runtime's bump cell / barrier buffer and heap.
-/

namespace FvModexp.Amd64.AsmWit

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

set_option maxRecDepth 100000

abbrev Memory := Janus.Arm64.Memory

theorem data_disj : DataSegsDisjoint Extracted.program.data := by unfold DataSegsDisjoint; decide +kernel

theorem data_lt : ∀ d ∈ Extracted.program.data, ∀ b ∈ d.bytes, b < 256 := by decide +kernel

theorem data_below : ∀ d ∈ Extracted.program.data, d.base + d.bytes.length ≤ 0xA00000 := by decide +kernel

def wbytes (f : Nat → Byte) (a : Nat) : Byte :=
  match dataSegByte Extracted.program.data a with
  | some n => BitVec.ofNat 8 n
  | none => f a

def dataRegs : List Janus.Arm64.Region := Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩

def wmem (f : Nat → Byte) (rs : List Janus.Arm64.Region) : Memory := ⟨wbytes f, rs ++ dataRegs⟩

theorem dataSegByte_high {a : Nat} (h : 0xA00000 ≤ a) : dataSegByte Extracted.program.data a = none := by
  unfold dataSegByte
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have := data_below d hd
  split
  · rename_i hc; omega
  · rfl

theorem wbytes_high (f : Nat → Byte) {a : Nat} (h : 0xA00000 ≤ a) : wbytes f a = f a := by
  unfold wbytes; rw [dataSegByte_high h]

theorem dataLoaded (f : Nat → Byte) (rs : List Janus.Arm64.Region) : Extracted.program.DataLoaded (wmem f rs) := by
  refine Program.DataLoaded_of_dataSegByte data_disj (fun d hd => ?_) data_lt fun a n h => ?_
  · have hb := data_below d hd
    refine List.any_eq_true.2 ⟨⟨d.base, d.bytes.length, false⟩, List.mem_append_right _ (List.mem_map_of_mem hd), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_false, Bool.and_true]
    exact ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, Nat.le_trans hb (by decide)⟩
  · show (wbytes f a).toNat = n % 256
    unfold wbytes; rw [h]; simp

def SP0 : Nat := 0xB00000
def G0 : Nat := 0xC00000
def T0 : Nat := 0xC80000
def OA : Nat := 0xD00000
def OB : Nat := 0xE00000
def RET : Nat := 0x1000

def stdRegs : List Janus.Arm64.Region :=
  [⟨SP0 - 0x2000, 0x2100, true⟩, ⟨G0, 0x100, false⟩, ⟨T0, 8, false⟩, ⟨OA, 0x1000, true⟩, ⟨OB, 0x1000, true⟩,
    ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩]

/-- `f` for the toy runtime and the TLS slot: the bump cell holds `HEAP` (byte 3 = `0x10`), the slot `[T0, T0+8)` holds
`G0` (byte 2 = `0xC0`), the return address `RET` sits at `SP0` (byte 1 = `0x10`); everything else is `g`. -/
def toyBytes (g : Nat → Byte) (a : Nat) : Byte :=
  if a = BUMP + 3 then 0x10 else if a = T0 + 2 then 0xC0 else if a = SP0 + 1 then 0x10 else if a < HEAP then g a else 0

abbrev R : RtInv := toyR [] fun _ _ => True

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem acc_eq (g : Nat → Byte) {rs : List Janus.Arm64.Region} (a n : Nat) (w : Bool) :
    (wmem g rs).accessible a n w = (wmem (fun _ => 0) rs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem roOut : RoOut R := by
  intro d hd
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]
  have : ∀ d' ∈ Extracted.program.data, (d'.base + d'.bytes.length ≤ HEAP ∨ HEND ≤ d'.base) ∧
      (d'.base + d'.bytes.length ≤ BUMP ∨ BUMP + 8 ≤ d'.base) ∧ (d'.base + d'.bytes.length ≤ WBUF ∨ WBUF + 64 ≤ d'.base) := by
    decide +kernel
  exact this d hd

theorem inv0 (g : Nat → Byte) (hbump : (wmem (toyBytes g) stdRegs).readLE BUMP 8 = HEAP) (gp : Nat) :
    R.inv 0x1000 [] gp (view R.rt [] (wmem (toyBytes g) stdRegs)) := by
  refine toyInv_init_live (m := wmem (toyBytes g) stdRegs) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) hbump (fun i hi hi' => ?_) (by rw [acc_eq (toyBytes g)]; decide +kernel)
    (by rw [acc_eq (toyBytes g)]; decide +kernel) (by rw [acc_eq (toyBytes g)]; decide +kernel)
  show wbytes (toyBytes g) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega), if_neg (by omega)]

end FvModexp.Amd64.AsmWit
