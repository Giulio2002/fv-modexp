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

/-- the read-only data lies outside the toy runtime's ranges -/
theorem roOut : RoOut R := by
  intro d hd
  rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]
  have : ∀ d' ∈ Extracted.program.data, (d'.base + d'.bytes.length ≤ HEAP ∨ HEND ≤ d'.base) ∧
      (d'.base + d'.bytes.length ≤ BUMP ∨ BUMP + 8 ≤ d'.base) ∧ (d'.base + d'.bytes.length ≤ WBUF ∨ WBUF + 64 ≤ d'.base) := by
    decide +kernel
  exact this d hd

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

/-! ## Call-site states of the runtime contracts (Janus U-WITNESS-CALLSITE)

A row witness must exhibit, for each contract hypothesis, a state at the contract's entry satisfying its precondition
(at the witness's `R`). `callS addr x y z`: a call with `X0..X2 = x, y, z` and the callee's frame just below `SP0`,
in the all-zero standard memory. -/

def memZ : Memory := wmem (toyBytes fun _ => 0) stdRegs

theorem bumpZ : memZ.readLE BUMP 8 = HEAP := by decide +kernel

def callS (addr x y z : Nat) : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 1 then BitVec.ofNat 64 y
      else if i = 2 then BitVec.ofNat 64 z else if i = 28 then BitVec.ofNat 64 G0
      else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 (SP0 - 16), pc := BitVec.ofNat 64 addr,
    flags := ⟨false, false, false, false⟩, mem := memZ }

@[simp] theorem cs_sp (a x y z : Nat) : (callS a x y z).sp = BitVec.ofNat 64 (SP0 - 16) := rfl
@[simp] theorem cs_mem (a x y z : Nat) : (callS a x y z).mem = memZ := rfl
@[simp] theorem cs_g (a x y z : Nat) : (callS a x y z).regs 28 = BitVec.ofNat 64 G0 := rfl
@[simp] theorem cs_lr (a x y z : Nat) : (callS a x y z).regs 30 = BitVec.ofNat 64 RET := rfl
@[simp] theorem cs_r0 (a x y z : Nat) : (callS a x y z).regs 0 = BitVec.ofNat 64 x := rfl
@[simp] theorem cs_r1 (a x y z : Nat) : (callS a x y z).regs 1 = BitVec.ofNat 64 y := rfl
@[simp] theorem cs_r2 (a x y z : Nat) : (callS a x y z).regs 2 = BitVec.ofNat 64 z := rfl

theorem memZ_acc (a n : Nat) (w : Bool) : memZ.accessible a n w = (wmem (fun _ => 0) stdRegs).accessible a n w :=
  acc_eq _ a n w

theorem cs_callOK (a x y z n : Nat) (hn : n ≤ 3) : CallOK (callS a x y z) 4096 n := by
  have hw : memZ.accessible (SP0 - 16 - 4096) (4096 + 8 + 8 * 3) true = true := by rw [memZ_acc]; decide +kernel
  have hs : (BitVec.ofNat 64 (SP0 - 16)).toNat = SP0 - 16 := by decide
  simp only [CallOK, cs_lr, cs_sp, cs_mem, hs]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by simp only [SP0]; omega, ?_⟩
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cs_guard (a x y z : Nat) : GuardOK (callS a x y z) 4096 := by
  simp only [GuardOK, cs_g, cs_mem, cs_sp]
  exact ⟨by decide, by rw [memZ_acc]; decide +kernel, by decide +kernel⟩

theorem cs_room (a x y z n : Nat) (hn : n ≤ 3) : StackRoom (callS a x y z) 4096 n := by
  refine ⟨cs_guard a x y z, ?_⟩
  simp only [calleeStack, cs_g, cs_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp only [G0, SP0]; omega

theorem cs_winR (a x y z n : Nat) (hn : n ≤ 3) : LiveSep (calleeStack (callS a x y z) 4096 n) R.rt := by
  intro x' hx
  simp only [calleeStack, cs_sp, List.mem_cons, List.not_mem_nil, or_false, BitVec.toNat_ofNat] at hx
  rw [rt_eq]
  rcases hx with rfl | rfl <;>
    simp only [outside_cons, outside_nil, and_true, SP0, HEAP, HEND, BUMP, WBUF, HSIZE] <;> omega

theorem cs_inv (a x y z : Nat) : R.inv 0x1000 [] ((callS a x y z).regs 28).toNat (view R.rt [] (callS a x y z).mem) :=
  inv0 _ bumpZ _

/-- the premise of `MemmoveLive` (and of the other live copy contracts) at a call -/
@[reducible] def mvSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  Mem.EqPre 4096 3 s ∧
  LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
  Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
  LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat

/-- a `memmove(OA, OB, 8)` call satisfies it -/
theorem site_mv (addr : Nat) : mvSite R addr [] 0x1000 (callS addr OA OB 8) := by
  have hcs : calleeStack (callS addr OA OB 8) 4096 3 =
      [(SP0 - 16 - 4096, SP0 - 16 - 8), (SP0 - 16 + 8, SP0 - 16 + 8 + 24)] := rfl
  refine ⟨⟨(guardOK_iff _ _).1 (cs_guard _ _ _ _), cs_callOK _ _ _ _ 3 (by omega), ?_⟩,
    ⟨trivial, cs_inv _ _ _ _, fun r hr => by simp at hr, cs_winR _ _ _ _ 3 (by omega)⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, Or.inr ?_⟩⟩
  all_goals simp only [hcs, cs_g, cs_mem, cs_r0, cs_r1, cs_r2, BitVec.toNat_ofNat]
  all_goals first
    | (simp only [outside_cons, outside_nil, and_true]; decide)
    | (rw [memZ_acc]; decide +kernel)
    | decide
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide)

/-- the premise of `MakesliceLiveContract` at a call -/
@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
      (s.regs 28).toNat s.mem (calleeStack s 4096 3)

/-- a `makeslice(Word, 1, 1)` call satisfies it (the `Word` type descriptor is read-only data of the extraction) -/
theorem site_mk (addr : Nat) : mkSite R addr [] 0x1000
    (callS addr Extracted.dataAddr.«type:big.Word#51b931e8» 1 1) := by
  refine ⟨⟨cs_callOK _ _ _ _ 3 (by omega), ?_, ?_, ?_, ?_⟩, cs_room _ _ _ _ 3 (by omega),
    trivial, cs_inv _ _ _ _, ?_, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 3 (by omega)⟩
  all_goals try simp only [makesliceRound, TypeOK, cs_mem, cs_r0, cs_r1, cs_r2, BitVec.toNat_ofNat]
  all_goals first | decide +kernel | exact ⟨by decide +kernel, by rw [memZ_acc]; decide +kernel⟩

end FvModexp.Arm64.AsmWit
