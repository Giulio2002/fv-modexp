import FvModexp.Proofs.Common.AsmCmp
import FvModexp.Proofs.Lib.CmpAmd64
import FvModexp.Proofs.Common.AsmEns64

/-!
# `math/big.nat.cmp(x, y nat) (r int)` (go-bigmodexpfix nat.go:152-180, Go ABIInternal, amd64): summary

Same algorithm as the arm64 summary (see `FvModexp.Arm64.CmpSum`). amd64 register arguments: `x = (RAX, RBX, RCX)`,
`y = (RDI, RSI, R8)`; result in `RAX`. Frame: `PUSHQ BP` (`[RSP-8, RSP)`) and the spill slots of `x.ptr` (`[RSP+8,+16)`)
and `y.ptr` (`[RSP+32,+40)`); no stack-growth prologue. Clobbers `RCX RDX RSI` and the flags.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.CmpAmd64 (program entry)

namespace FvModexp.Amd64.CmpSum

abbrev head : Nat := entry + 0x40
abbrev exitPc : Nat := entry + 0x52

/-- the result of `nat.cmp` as the 64-bit word in `RAX` -/
def cmpRes (m n X Y : Nat) : BitVec 64 :=
  if m < n then 18446744073709551615#64 else if n < m then 1#64
  else if X < Y then 18446744073709551615#64 else if Y < X then 1#64 else 0#64

/-- the stack written: saved `RBP` `[RSP-8, RSP)`, spill slots of `x.ptr` and `y.ptr` -/
def frame (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16),
    ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)]

/-- a slice argument the function may read: empty, or readable and outside the stack window `[RSP-8, RSP+40)` -/
def SliceOK (s : State) (p n : Nat) : Prop :=
  n = 0 ∨ (s.mem.accessible p (8 * n) false = true ∧ Apart p (8 * n) ((s.regs 4).toNat - 8) 48)

def Pre (s : State) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.accessible ((s.regs 4).toNat - 8) 48 true = true ∧
  SliceOK s (s.regs 0).toNat (s.regs 3).toNat ∧ SliceOK s (s.regs 7).toNat (s.regs 6).toNat

def Post (s s' : State) : Prop :=
  ∃ (v1 v2 v6 : BitVec 64) (f : Flags) (m : Memory),
    s' = { s with regs := setRegF (setRegF (setRegF (setRegF (setRegF s.regs 0
              (cmpRes (s.regs 3).toNat (s.regs 6).toNat (lv s.mem (s.regs 0).toNat (s.regs 3).toNat)
                (lv s.mem (s.regs 7).toNat (s.regs 6).toNat))) 1 v1) 2 v2) 4 (s.regs 4 + 8#64)) 6 v6,
                  rip := retAddrOf s, flags := f, mem := m } ∧
    MemFrame s.mem m (frame s)

theorem res_lt (m : Memory) (x y k n : Nat) (hk : k < n) (ht : top m x k n = top m y k n)
    (hl : ¬ m.readLE (y + k * 8) 8 ≤ m.readLE (x + k * 8) 8) : cmpRes n n (lv m x n) (lv m y n) = 18446744073709551615#64 := by
  have := lv_lt_of_top m x y k n hk ht (by rw [Nat.mul_comm 8 k]; omega)
  simp [cmpRes, this]

theorem res_gt (m : Memory) (x y k n : Nat) (hk : k < n) (ht : top m x k n = top m y k n)
    (hl : ¬ m.readLE (x + k * 8) 8 ≤ m.readLE (y + k * 8) 8) : cmpRes n n (lv m x n) (lv m y n) = 1#64 := by
  have := lv_lt_of_top m y x k n hk ht.symm (by rw [Nat.mul_comm 8 k]; omega)
  simp [cmpRes, this, Nat.lt_asymm this]

theorem res_eq (m : Memory) (x y n : Nat) (hn : 0 < n) (ht : top m x 0 n = top m y 0 n)
    (h1 : m.readLE y 8 ≤ m.readLE x 8) (h2 : m.readLE x 8 ≤ m.readLE y 8) :
    cmpRes n n (lv m x n) (lv m y n) = 0#64 := by
  have := lv_eq_of_top m x y n hn ht (by omega)
  simp [cmpRes, this]

/-- the loop registers: `RCX = k`, `RDX`, `RSI` scratch, `RSP = RBP = SP - 8` -/
abbrev regsL (s : State) (k : Nat) (v2 v6 : BitVec 64) : Nat → BitVec 64 :=
  setRegF (setRegF (setRegF (setRegF (setRegF s.regs 1 (BitVec.ofNat 64 k)) 2 v2) 4 (s.regs 4 - 8#64))
    5 (s.regs 4 - 8#64)) 6 v6

theorem exit_lem (s : State) (hmn : (s.regs 3).toNat = (s.regs 6).toNat) (hpos : 0 < (s.regs 3).toNat)
    (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hb : 8 ≤ (s.regs 4).toNat) (hbb : (s.regs 4).toNat + 40 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 8) 48 true = true)
    (hax : s.mem.accessible (s.regs 0).toNat (8 * (s.regs 3).toNat) false = true)
    (hay : s.mem.accessible (s.regs 7).toNat (8 * (s.regs 3).toNat) false = true)
    (hxa : Apart (s.regs 0).toNat (8 * (s.regs 3).toNat) ((s.regs 4).toNat - 8) 48)
    (hya : Apart (s.regs 7).toNat (8 * (s.regs 3).toNat) ((s.regs 4).toNat - 8) 48)
    (M : Memory) (hM : MemFrame s.mem M (frame s))
    (h_rd5 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (h_rdr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) :
    ∀ k (R : Nat → BitVec 64) (P : BitVec 64) (f : Flags) (v2 v6 : BitVec 64), k < (s.regs 3).toNat →
      P = BitVec.ofNat 64 exitPc →
      top s.mem (s.regs 0).toNat k (s.regs 3).toNat = top s.mem (s.regs 7).toNat k (s.regs 3).toNat →
      (k = 0 ∨ s.mem.readLE ((s.regs 0).toNat + k * 8) 8 ≠ s.mem.readLE ((s.regs 7).toNat + k * 8) 8) →
      R = regsL s k v2 v6 →
      ReachesRet program (retAddrOf s) { s with regs := R, rip := P, flags := f, mem := M } (Post s) := by
  have bx := Arm64.Memory.accessible_bound _ hax
  have by' := Arm64.Memory.accessible_bound _ hay
  intro k R P f v2 v6 hk hP ht hne hR
  subst hR hP
  simp only [exitPc, FvModexp.Lib.CmpAmd64.entry, Nat.reduceAdd]
  have h_rdx : M.readLE ((s.regs 0).toNat + k * 8) 8 = s.mem.readLE ((s.regs 0).toNat + k * 8) 8 :=
    hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hxa; omega)
  have h_rdy : M.readLE ((s.regs 7).toNat + k * 8) 8 = s.mem.readLE ((s.regs 7).toNat + k * 8) 8 :=
    hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hya; omega)
  have hxl := FvModexp.Asm.limb_lt s.mem ((s.regs 0).toNat + k * 8)
  have hyl := FvModexp.Asm.limb_lt s.mem ((s.regs 7).toNat + k * 8)
  janus64_run
  all_goals (unfold Post; rw [← hmn])
  all_goals
    rcases Nat.lt_trichotomy (s.mem.readLE ((s.regs 0).toNat + k * 8) 8)
      (s.mem.readLE ((s.regs 7).toNat + k * 8) 8) with h | h | h
    · first
        | (rw [res_lt s.mem (s.regs 0).toNat (s.regs 7).toNat k _ hk ht (by omega)]
           exact ⟨_, _, _, _, _, rfl, hM⟩)
        | (exfalso; omega)
    · first
        | (exfalso; omega)
        | (have hk0 : k = 0 := by rcases hne with h' | h'; exact h'; exact absurd h h'
           subst hk0
           simp only [Nat.zero_mul, Nat.add_zero] at h ht
           rw [res_eq s.mem _ _ _ hpos ht (by omega) (by omega)]
           exact ⟨_, _, _, _, _, rfl, hM⟩)
    · first
        | (rw [res_gt s.mem (s.regs 0).toNat (s.regs 7).toNat k _ hk ht (by omega)]
           exact ⟨_, _, _, _, _, rfl, hM⟩)
        | (exfalso; omega)

theorem loop (s : State) (hmn : (s.regs 3).toNat = (s.regs 6).toNat) (hpos : 0 < (s.regs 3).toNat)
    (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hb : 8 ≤ (s.regs 4).toNat) (hbb : (s.regs 4).toNat + 40 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 8) 48 true = true)
    (hax : s.mem.accessible (s.regs 0).toNat (8 * (s.regs 3).toNat) false = true)
    (hay : s.mem.accessible (s.regs 7).toNat (8 * (s.regs 3).toNat) false = true)
    (hxa : Apart (s.regs 0).toNat (8 * (s.regs 3).toNat) ((s.regs 4).toNat - 8) 48)
    (hya : Apart (s.regs 7).toNat (8 * (s.regs 3).toNat) ((s.regs 4).toNat - 8) 48)
    (M : Memory) (hM : MemFrame s.mem M (frame s))
    (h_rd5 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (h_rdr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) :
    ∀ k (R : Nat → BitVec 64) (P : BitVec 64) (f : Flags) (v2 v6 : BitVec 64), k < (s.regs 3).toNat →
      P = BitVec.ofNat 64 head →
      top s.mem (s.regs 0).toNat k (s.regs 3).toNat = top s.mem (s.regs 7).toNat k (s.regs 3).toNat →
      R = regsL s k v2 v6 →
      ReachesRet program (retAddrOf s) { s with regs := R, rip := P, flags := f, mem := M } (Post s) := by
  have bx := Arm64.Memory.accessible_bound _ hax
  have by' := Arm64.Memory.accessible_bound _ hay
  have hex := exit_lem s hmn hpos hr hb hbb hw hax hay hxa hya M hM h_rd5 h_rdr
  intro k
  induction k with
  | zero =>
    intro R P f v2 v6 hk hP ht hR
    subst hR hP
    simp only [head, FvModexp.Lib.CmpAmd64.entry, Nat.reduceAdd]
    janus64_run until [entry + 0x52]
    exact hex 0 _ _ _ _ _ hk rfl ht (Or.inl rfl) rfl
  | succ k ih =>
    intro R P f v2 v6 hk hP ht hR
    subst hR hP
    simp only [head, FvModexp.Lib.CmpAmd64.entry, Nat.reduceAdd]
    have h_rdx : M.readLE ((s.regs 0).toNat + (k + 1) * 8) 8 = s.mem.readLE ((s.regs 0).toNat + (k + 1) * 8) 8 :=
      hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hxa; omega)
    have h_rdy : M.readLE ((s.regs 7).toNat + (k + 1) * 8) 8 = s.mem.readLE ((s.regs 7).toNat + (k + 1) * 8) 8 :=
      hM.readLE _ _ (by simp only [frame, outside_cons, outside_nil, and_true]; unfold Apart at hya; omega)
    have hsub : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hxl := FvModexp.Asm.limb_lt s.mem ((s.regs 0).toNat + (k + 1) * 8)
    have hyl := FvModexp.Asm.limb_lt s.mem ((s.regs 7).toNat + (k + 1) * 8)
    have hmsb : (BitVec.ofNat 64 (k + 1)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    janus64_run until [entry + 0x40, entry + 0x52]
    · rw [hmsb] at hbr; cases hbr
    · have heq : s.mem.readLE ((s.regs 7).toNat + (k + 1) * 8) 8 = s.mem.readLE ((s.regs 0).toNat + (k + 1) * 8) 8 := by
        omega
      refine ih _ _ _ ?v2 ?v6 (by omega) (by decide) ?ht ?hR
      case hR =>
        simp only [regsL]; rw [hsub]
      case ht => rw [top_step s.mem _ k _ (by omega), top_step s.mem _ k _ (by omega), ht, Nat.mul_comm 8 (k + 1), heq]
    · refine hex (k + 1) _ _ _ _ _ hk (by decide) ht (Or.inr fun h => hbr ?_) rfl
      rw [h]; omega

theorem post_intro (s : State) (R : BitVec 64) (f : Flags) (m : Memory)
    (hR : R = cmpRes (s.regs 3).toNat (s.regs 6).toNat (lv s.mem (s.regs 0).toNat (s.regs 3).toNat)
      (lv s.mem (s.regs 7).toNat (s.regs 6).toNat))
    (hm : MemFrame s.mem m (frame s)) :
    Post s ({ s with regs := setRegF (setRegF s.regs 0 R) 4 (s.regs 4 + 8#64), rip := retAddrOf s, flags := f, mem := m }) := by
  refine ⟨s.regs 1, s.regs 2, s.regs 6, f, m, ?_, hm⟩
  subst hR
  congr 1
  funext j
  simp only [setRegF]
  by_cases h1 : j = 1
  · subst h1; simp
  · by_cases h2 : j = 2
    · subst h2; simp
    · by_cases h6 : j = 6
      · subst h6; simp
      · simp [h1, h2, h6]

theorem regs_init (r : Nat → BitVec 64) (a b : BitVec 64) :
    setRegF (setRegF (setRegF r 1 a) 4 b) 5 b = setRegF (setRegF (setRegF (setRegF (setRegF r 1 a) 2 (r 2)) 4 b) 5 b) 6 (r 6) := by
  funext j
  simp only [setRegF]
  by_cases h2 : j = 2
  · subst h2; simp
  · by_cases h6 : j = 6
    · subst h6; simp
    · simp [h2, h6]

theorem cmp_summary : Summary program entry Pre Post := by
  intro s hpc ⟨hr, hb, hbb, hw, hsx, hsy⟩
  have hmb : (s.regs 3).toNat ≤ 2 ^ 45 := by
    rcases hsx with h | ⟨h, _⟩
    · omega
    · have := Arm64.Memory.accessible_bound _ h; omega
  have hnb : (s.regs 6).toNat ≤ 2 ^ 45 := by
    rcases hsy with h | ⟨h, _⟩
    · omega
    · have := Arm64.Memory.accessible_bound _ h; omega
  rcases Nat.eq_zero_or_pos (s.regs 3).toNat with hm0 | hpos
  · rcases Nat.eq_zero_or_pos (s.regs 6).toNat with hn0 | hnpos
    all_goals janus64_run until [head]
    all_goals
      refine post_intro s _ _ _ ?_ ?_
      · simp only [cmpRes, hm0, lv_zero]
        try simp only [hn0, lv_zero]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      · unfold frame; janus_frame
  janus64_run until [head]
  all_goals try (
      refine post_intro s _ _ _ ?_ ?_
      · simp only [cmpRes]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      · unfold frame; janus_frame)
  have hmn : (s.regs 3).toNat = (s.regs 6).toNat := by omega
  obtain ⟨hax, hxa⟩ := hsx.resolve_left (by omega)
  obtain ⟨hay, hya⟩ := hsy.resolve_left (by omega)
  rw [← hmn] at hay hya
  have hsub : s.regs 3 - 1#64 = BitVec.ofNat 64 ((s.regs 3).toNat - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine loop s hmn hpos hr hb hbb hw hax hay hxa hya _ (by unfold frame; janus_frame) ?_ ?_
    ((s.regs 3).toNat - 1) _ _ _ _ _ (by omega) (by decide)
    (by rw [top_last _ _ _ hpos, top_last _ _ _ hpos]) (by rw [hsub, regs_init])
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]

/-- the standalone contract (statement in Janus vocabulary only) -/
theorem ensures (x xl xc y yl yc : BitVec 64) :
    Ensures program entry [x, xl, xc, y, yl, yc]
      (fun s => 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat - 8) 48 true = true ∧
        (xl.toNat = 0 ∨ (s.mem.accessible x.toNat (8 * xl.toNat) false = true ∧
          Apart x.toNat (8 * xl.toNat) ((s.regs 4).toNat - 8) 48)) ∧
        (yl.toNat = 0 ∨ (s.mem.accessible y.toNat (8 * yl.toNat) false = true ∧
          Apart y.toNat (8 * yl.toNat) ((s.regs 4).toNat - 8) 48)))
      (fun s s' => results 1 s' =
          [if xl.toNat < yl.toNat then 18446744073709551615#64 else if yl.toNat < xl.toNat then 1#64
            else if s.mem.readLE x.toNat (8 * xl.toNat) < s.mem.readLE y.toNat (8 * yl.toNat) then 18446744073709551615#64
            else if s.mem.readLE y.toNat (8 * yl.toNat) < s.mem.readLE x.toNat (8 * xl.toNat) then 1#64 else 0#64] ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16),
          ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)]) := by
  refine ensures_of_summary64 cmp_summary ?_ ?_
  · intro ret s hret hsu ⟨hb, hbb, hw, hx, hy⟩
    have h0 : s.regs 0 = x := by have := hsu.args 0 (by simp); simpa using this
    have h3 : s.regs 3 = xl := by have := hsu.args 1 (by simp); simpa using this
    have h7 : s.regs 7 = y := by have := hsu.args 3 (by simp); simpa using this
    have h6 : s.regs 6 = yl := by have := hsu.args 4 (by simp); simpa using this
    have hr := hsu.ret
    simp only [Amd64.Program.withExit, Janus.Amd64.GoABI.regSP] at hr
    refine ⟨by rw [hr]; exact hret.user, hb, hbb, hw, ?_, ?_⟩
    · unfold SliceOK; rw [h0, h3]; exact hx
    · unfold SliceOK; rw [h7, h6]; exact hy
  · intro ret s s' hret hsu _ ⟨v1, v2, v6, f, m, he, hf⟩
    have h0 : s.regs 0 = x := by have := hsu.args 0 (by simp); simpa using this
    have h3 : s.regs 3 = xl := by have := hsu.args 1 (by simp); simpa using this
    have h7 : s.regs 7 = y := by have := hsu.args 3 (by simp); simpa using this
    have h6 : s.regs 6 = yl := by have := hsu.args 4 (by simp); simpa using this
    subst he
    refine ⟨⟨by simp [setRegF, Janus.Amd64.GoABI.regSP], by simp [setRegF, Janus.Amd64.GoABI.regFP],
      by simp [setRegF, Janus.Amd64.GoABI.regG], rfl⟩, ?_, hf⟩
    simp only [results]
    simp [Janus.Amd64.GoABI.intArgRegs, setRegF, cmpRes, lv, h0, h3, h7, h6]

end FvModexp.Amd64.CmpSum
