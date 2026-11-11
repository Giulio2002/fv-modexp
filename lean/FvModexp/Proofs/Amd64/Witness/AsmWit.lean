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

/-! ## `ImplApart` without a per-byte decision

`decide` on `ImplApart Extracted.program impl` checks every code byte against the stub list (> 10 min on the amd64 Run
extraction). `implApart_of_info`: the segments' `[base, end)` ranges (computed once, `info_eq`) pairwise disjoint, every
stub address and the exit address outside them. -/

def info (segs : List Amd64.Segment) : List (Nat × Nat) := segs.map fun s => (s.base, s.base + s.bytes.length)

/-- the code ranges of the amd64 Run extraction (generated from `Extracted.lean`) -/
def infoLit : List (Nat × Nat) := [(0x654340, 0x654fed), (0x4eaa80, 0x4eac36), (0x5ed6e0, 0x5ed896), (0x5e2d60, 0x5e2fde), (0x5e3080, 0x5e317a), (0x5e3180, 0x5e3733), (0x5e2b40, 0x5e2c9e), (0x5e2800, 0x5e29cc), (0x5e2620, 0x5e27ec), (0x5e5060, 0x5e54ae), (0x5e2560, 0x5e260c), (0x5e6fa0, 0x5e79d3), (0x5e58e0, 0x5e5ca5), (0x5edf20, 0x5ee465), (0x5e5560, 0x5e58d9), (0x5e5cc0, 0x5e5d46), (0x5e3740, 0x5e3cb7), (0x5e2fe0, 0x5e3076), (0x5e54c0, 0x5e554b), (0x5edca0, 0x5edecd), (0x5e7a20, 0x5e826d), (0x5eaf40, 0x5eb05b), (0x5e8fa0, 0x5e92b9), (0x5e8280, 0x5e88b6), (0x5f2c60, 0x5f2cff), (0x5f2a20, 0x5f2bb6), (0x5ee4c0, 0x5ee74e), (0x5ee920, 0x5ef185), (0x5f2bc0, 0x5f2c5f), (0x5f2880, 0x5f2a16), (0x5e41c0, 0x5e5057), (0x5e6480, 0x5e660c), (0x5f0fe0, 0x5f145f), (0x5f0840, 0x5f0f45), (0x5eb060, 0x5ec3a5), (0x5ec400, 0x5ed68f), (0x5e92c0, 0x5e9dd2), (0x5e9e20, 0x5ea872), (0x5e69c0, 0x5e6d17), (0x5e6620, 0x5e69b6), (0x5ed8a0, 0x5edc85), (0x5ea8c0, 0x5eaf38), (0x5e6d20, 0x5e6f85), (0x5ee760, 0x5ee90a), (0x5f2d00, 0x5f2dc2), (0x5ef880, 0x5f07e8), (0x5ef1e0, 0x5ef833), (0x5f2de0, 0x5f2e96), (0x5e3cc0, 0x5e3e30), (0x5e3e40, 0x5e40b9), (0x5e40c0, 0x5e41bb), (0x5e29e0, 0x5e2b25), (0x5e2ca0, 0x5e2d45), (0x5f1940, 0x5f1b38), (0x5f1b40, 0x5f1d85), (0x5f14a0, 0x5f18fe), (0x5f2380, 0x5f2826), (0x5f1da0, 0x5f2337), (0x5e62c0, 0x5e63ed), (0x5e5d60, 0x5e62bd), (0x5e8900, 0x5e8f8a), (0x5e2480, 0x5e2544), (0x5f2ea0, 0x5f2f55), (0x5f2f60, 0x5f31b9), (0x4901c0, 0x4901cb), (0x5e79e0, 0x5e7a1a), (0x5ee480, 0x5ee4ba), (0x5edee0, 0x5edf06), (0x5e88c0, 0x5e88e6), (0x5ef1a0, 0x5ef1c6), (0x5f1460, 0x5f149a), (0x5f0fa0, 0x5f0fda), (0x5f0f60, 0x5f0f86), (0x5ec3c0, 0x5ec3e6), (0x5ed6a0, 0x5ed6c6), (0x5e9de0, 0x5e9e06), (0x5ea880, 0x5ea8a6), (0x5f0800, 0x5f0826), (0x5ef840, 0x5ef866), (0x5f1900, 0x5f1926), (0x5f2840, 0x5f2866), (0x5f2340, 0x5f2366)]

theorem info_eq : info Extracted.program.segments = infoLit := by decide +kernel

theorem implApart_of_info {P : Amd64.Program} {I : List (Nat × Nat)} (hI : info P.segments = I)
    (h1 : I.Pairwise fun a b => a.2 ≤ b.1 ∨ b.2 ≤ a.1)
    (h2 : ∀ a ∈ P.stubs.map (·.addr), ∀ q ∈ I, a < q.1 ∨ q.2 ≤ a) (h3 : ∀ q ∈ I, P.exitAddr < q.1) :
    Amd64.ImplApart P [] := by
  subst hI
  refine ⟨?_, fun seg hseg i hi => ?_⟩
  · rw [List.append_nil]
    unfold info at h1
    rw [List.pairwise_map] at h1
    exact h1.imp fun h => by unfold Amd64.Segment.Apart; simpa using h
  · rw [List.append_nil] at hseg
    have hq : (seg.base, seg.base + seg.bytes.length) ∈ info P.segments := List.mem_map_of_mem hseg
    refine ⟨?_, ?_⟩
    · unfold Amd64.Program.stubAt
      rw [List.find?_eq_none]
      intro st hst
      have := h2 st.addr (List.mem_map_of_mem hst) _ hq
      simp only [decide_eq_true_eq]
      omega
    · have := h3 _ hq; simp only at this; omega

theorem implApart_nil : Amd64.ImplApart Extracted.program [] :=
  implApart_of_info info_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FvModexp.Amd64.AsmWit
