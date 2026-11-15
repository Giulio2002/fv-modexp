import FvModexp.Proofs.Amd64.Top.RunDEDefs
import FvModexp.Proofs.Amd64.Top.RunBox

/-!
# `Run` (amd64): the padded operand buffers — the join `J j` before `RightPadBytes`' copy

When operand `j` (0 base, 1 exp, 2 mod) is longer than what is left of the input, `getData` + `RightPadBytes`
allocate a zeroed buffer of `size = opLen j` bytes — the 32-byte stack buffer `e - 392 - 32 j` (`size ≤ 32`) or a
fresh `makeslice(uint8, size, size)` object — and copy the `opAvail j` available input bytes into its front. The code
paths meet at `J j` (right after the `CMOVG` computing the copy size): `CMPQ dst, src; JE` (skip) or
`memmove(dst, src, n)`, then the `setBytes` call `pcE j`.

* `JoinE … j … dst src S`: the state at `J j` (`RelD` at slot level `j`, the zeroed buffer, the source in the input,
  the live set split `Lk = L0 ++ Lb` with the fresh buffer object `Lb` apart from the older objects `L0`).
* `AtE … j S`: the state at the `setBytes` call `pcE j` that `dE j` (RunDE*) consumes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

abbrev pcJ0 : Nat := segAddr Extracted.program fn + 0x6a2
abbrev pcJ1 : Nat := segAddr Extracted.program fn + 0x840
abbrev pcJ2 : Nat := segAddr Extracted.program fn + 0x9c7

/-- The number of input bytes of operand `j` (the `copy` length of `RightPadBytes`). -/
@[reducible] def opAvail (s : State) (p len : BitVec 64) (j : Nat) : Nat :=
  min (opLen s p len j) (len.toNat - 96 - opStart s p len j)

/-- The 32-byte stack buffer of operand `j`. -/
@[reducible] def stkBuf (s : State) (j : Nat) : Nat := (s.regs 4).toNat - 392 - 32 * j

/-- The fresh `makeslice` buffer object `[dst, e)` of a padded operand: a runtime object outside the frame window. -/
def FreshDst (R : RtInv) (s : State) (size dst e : Nat) : Prop :=
  dst + size ≤ e ∧ InRanges dst (e - dst) R.rt ∧ Outside dst (e - dst) (win s stk 40)

/-- The state at the join `J j`: the live set is `L0 ++ Lb` where `Lb` is the buffer object (`[]` for the stack
buffer `stkBuf s j`, `[(dst, e)]` for a fresh one), apart from the older objects `L0`. -/
def JoinE (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret j : Nat)
    (L0 Lb : List (Nat × Nat)) (bk dst src : Nat) (S : State) : Prop :=
  RelD R b L c p len cp s ret j j (cstE j) (L0 ++ Lb) bk S ∧
  (j = 0 → S.mem.readLE ((s.regs 4).toNat - 512) 8 = min (hdrV s p len 0) (len.toNat - 96)) ∧
  (∀ i, i < opLen s p len j → S.mem.readLE (dst + i) 1 = 0) ∧
  p.toNat ≤ src ∧ src + opAvail s p len j ≤ p.toNat + len.toNat ∧
  (0 < opAvail s p len j → src = p.toNat + 96 + opStart s p len j) ∧
  dst + opLen s p len j ≤ 2 ^ 48 ∧ s.mem.accessible dst (opLen s p len j) true = true ∧
  LiveExt R L L0 ∧ LiveSep L0 Lb ∧ (∀ i, i < j → OpDone R S.mem s p len L L0 i)

/-- The state at operand `j`'s `setBytes` call: what `dE j` needs. -/
def AtE (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) (ret j pc : Nat)
    (S : State) : Prop :=
  ∃ Lk bk, RelD R b L c p len cp s ret j (j + 1) (cstE j) Lk bk S ∧ S.rip = BitVec.ofNat 64 pc ∧
    S.regs 0 = 0#64 ∧ S.regs 3 = 0#64 ∧ S.regs 1 = 0#64 ∧
    BufOK R Lk s S.mem p len j (S.regs 7).toNat (S.regs 6).toNat

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run

/-- A pointer into (or one past) the input is not a frame slot: the input is outside the window. -/
theorem src_ne_frame {e p l src n k : Nat} (hp : p ≤ src) (hs : src + n ≤ p + l)
    (hpw : p + l ≤ e - 4800 ∨ e + 40 ≤ p) (he : 4800 ≤ e) (hk : k < 4800) (hk0 : 0 < k) : src ≠ e - k := by
  omega

/-- A stack range `[e - k, e - k + n)` inside the frame window `[e - 4800, e + 40)`. -/
theorem buf_in_win {e n k : Nat} (he : 4800 ≤ e) (hk : k ≤ 4800) (hkn : n ≤ k + 40) :
    e - 4800 ≤ e - k ∧ e - k + n ≤ e - 4800 + (4800 + 40) := by omega

theorem win_len {e : Nat} (he : 4800 ≤ e) : e - 4800 + (e + 40 - (e - 4800)) ≤ e - 4800 + (4800 + 40) := by omega

/-- A live object outside the frame window is apart from a stack range inside it. -/
theorem win_out_buf {e n k a l : Nat} (he : 4800 ≤ e) (hk : k ≤ 4800) (hkn : n ≤ k + 40)
    (h : a + l ≤ e - 4800 ∨ e + 40 ≤ a) : a + l ≤ e - k ∨ e - k + n ≤ a := by omega

/-- The source of operand 0's copy (`input[96:]` at `p + inOff len`) and its `opAvail`. -/
theorem src_facts0 (p len : BitVec 64) (h0 : Nat) (hp : p.toNat + len.toNat ≤ 2 ^ 48) :
    p.toNat ≤ p.toNat + inOff len ∧ p.toNat + inOff len + min h0 (len.toNat - 96) ≤ p.toNat + len.toNat ∧
    (0 < min h0 (len.toNat - 96) → p.toNat + inOff len = p.toNat + 96 + 0) := by
  unfold inOff; split <;> omega

/-- The slots of operand `j`'s `big.Int` (`opAt s j = e - 136 - 32 j`) in normal form. -/
theorem opAt_eqs {e j : Nat} (he : 4800 ≤ e) (hj : j ≤ 2) :
    e - 136 - 32 * j = e - (136 + 32 * j) ∧ e - 136 - 32 * j + 8 = e - (128 + 32 * j) ∧
      e - 136 - 32 * j + 16 = e - (120 + 32 * j) ∧ e - 136 - 32 * j + 24 = e - (112 + 32 * j) := by omega

theorem cw_le {e k : Nat} (he : 4800 ≤ e) (hk : k ≤ 568) : e - 616 + 48 ≤ e - k := by omega

theorem beVal_writeLE_disj {m : Janus.Arm64.Memory} {a k v d n : Nat} (h : d + n ≤ a ∨ a + k ≤ d) :
    beVal (m.writeLE a k v) d n = beVal m d n := by
  apply beVal_congr
  intro i hi
  have := Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) (a := a) (n := k) (b := d + i) (k := 1) v (by omega)
  simp only [Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

theorem slot_lt {e a b k : Nat} (he : 4800 ≤ e) (ha : a ≤ 4800) (h : b + k ≤ a) : e - a + k ≤ e - b := by omega

/-- Byte `i` of a stack buffer `e - k` (`k ∈ [392, 456]`, `i < 32`): inside the window, outside the callee stack
`[e - 616 - 4096, e - 584)`, below the spill slots `e - 264 … e - 240`. -/
theorem buf_byte {e k i : Nat} (he : 4800 ≤ e) (hk : k ≤ 456) (hk2 : 392 ≤ k) (hi : i < 32) :
    e - 4800 ≤ e - k + i ∧ e - k + i + 1 ≤ e - 4800 + (4800 + 40) ∧
    (e - k + i + 1 ≤ e - 616 - 4096 ∨ e - 616 ≤ e - k + i) ∧
    (e - k + i + 1 ≤ e - 616 + 8 ∨ e - 616 + 8 + 24 ≤ e - k + i) ∧
    (e - k + i + 1 ≤ e - 616 ∨ e - 616 + 8 ≤ e - k + i) := by
  omega

/-- A byte below the spill slots `e - 264 … e - 240`. -/
theorem buf_byte_w {e k i w : Nat} (he : 4800 ≤ e) (hk : k ≤ 456) (hk2 : 392 ≤ k) (hi : i < 32) (hw : 248 ≤ w)
    (hw2 : w ≤ 264) : e - k + i + 1 ≤ e - w ∨ e - w + 8 ≤ e - k + i := by omega

/-- A byte of the input (outside the window) is apart from an 8-byte frame slot `e - w`. -/
theorem in_byte_out {p l a e w : Nat} (he : 4800 ≤ e) (hw : 8 ≤ w) (hw2 : w ≤ 4800) (hp : p ≤ a) (ha : a + 1 ≤ p + l)
    (h : p + l ≤ e - 4800 ∨ e + 40 ≤ p) : a + 1 ≤ e - w ∨ e - w + 8 ≤ a := by omega

theorem in_rng {p l i h0 st : Nat} (hi : i < min h0 (l - 96 - st)) :
    p ≤ p + 96 + st + i ∧ p + 96 + st + i + 1 ≤ p + l := by omega

theorem liveSep_of_apartAll {L : List (Nat × Nat)} {ptr round : Nat} (h : ApartAll ptr round L) :
    LiveSep L [(ptr, ptr + round)] := by
  intro r hr
  have := h r hr
  unfold Apart at this
  simp only [Janus.outside_cons, Janus.outside_nil, and_true]
  omega

/-- A fresh runtime object is outside the frame window. -/
theorem fresh_out_win {R : RtInv} {s : State} {ptr round : Nat} (he : 4800 ≤ (s.regs 4).toNat)
    (hIn : InRanges ptr round R.rt) (hout : Outside ((s.regs 4).toNat - 4800) (4800 + 40) R.rt) :
    Outside ptr round (win s stk 40) := by
  have := InRanges.apart hIn hout
  unfold Apart at this
  simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true]
  omega

theorem bud_alloc {b b1 c r A c' : Nat} (h : b - c ≤ b1) (hr : r ≤ A) (hA : c + A ≤ c') (hb : c' ≤ b) :
    b - c' ≤ b1 - r := by omega

/-- A fresh buffer `[dst, dst + n)` (outside the frame window): apart from the callee stack of a call from `Run`'s
frame and from the spill slots. -/
theorem fresh_call_facts {e dst n : Nat} (he : 4800 ≤ e) (h : dst + n ≤ e - 4800 ∨ e + 40 ≤ dst) :
    (dst + n ≤ e - 616 - 4096 ∨ e - 616 ≤ dst) ∧ (dst + n ≤ e - 616 + 8 ∨ e - 616 + 8 + 24 ≤ dst) ∧
    (dst + n ≤ e - 616 ∨ e - 616 + 8 ≤ dst) ∧ (dst + n ≤ e - 616 - 4160 ∨ e - 616 + 48 ≤ dst) := by omega

/-- Byte `i` of a fresh buffer outside the window is apart from an 8-byte frame slot `e - w`. -/
theorem fresh_byte_out {e dst i w x : Nat} (he : 4800 ≤ e) (hw : 8 ≤ w) (hw2 : w ≤ 4800)
    (h : dst + x ≤ e - 4800 ∨ e + 40 ≤ dst) (hi : i < x) : dst + i + 1 ≤ e - w ∨ e - w + 8 ≤ dst + i := by omega

theorem liveSep_single_sub {L : List (Nat × Nat)} {a e n : Nat} (h : LiveSep L [(a, e)]) (hn : a + n ≤ e) :
    LiveSep L [(a, a + n)] := by
  intro r hr
  have := h r hr
  simp only [Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
  omega

theorem fresh_slot {e dst x n w : Nat} (he : 4800 ≤ e) (hw : 8 ≤ w) (hw2 : w ≤ 4800)
    (h : dst + x ≤ e - 4800 ∨ e + 40 ≤ dst) (hn : n ≤ x) : dst + n ≤ e - w ∨ e - w + 8 ≤ dst := by omega

theorem lt_sub_of_add {i h dst e : Nat} (h2 : i < h) (hfe : dst + h ≤ e) : i < e - dst := by omega

/-- A fresh buffer at the copy source: nothing is copied (the source would be an input byte inside the new object). -/
theorem n0_of_eq {R : RtInv} {L L0 : List (Nat × Nat)} {dst src e h0 n p l : Nat} (heq : dst = src)
    (hfe : dst + h0 ≤ e) (hfrt : InRanges dst (e - dst) R.rt) (hheld : Held R L p l) (hext : LiveExt R L L0)
    (hsep : LiveSep L0 [(dst, e)]) (hsrc : 0 < n → src = p + 96 + 0) (hs : src + n ≤ p + l) (hn : n ≤ h0) :
    n = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact h
  · exfalso
    have hs' := hsrc h
    rcases hheld with ⟨r, hr, h1, h2⟩ | hout
    · have := hsep r (hext.mem_old hr)
      simp only [Janus.outside_cons, Janus.outside_nil, and_true] at this
      omega
    · obtain ⟨r, hr, h1, h2⟩ := hfrt
      have := MemFrame.outside_mem hout hr
      omega

theorem toNat_sub_k {x : BitVec 64} {k : Nat} (h : k ≤ x.toNat) (hk : k < 2 ^ 64) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; omega

/-- The stack-guard and alignment facts of a runtime contract call from `Run`'s frame (`RSP = e - 608`). -/
theorem frame_call_facts {e g gv : Nat} (hal : e % 8 = 0) (hg3 : gv + 4800 < e)
    (hga : g + 16 + 8 ≤ e - 4800 ∨ e - 4800 + (4800 + 40) ≤ g + 16) :
    (e - 616) % 8 = 0 ∧ gv + 4096 < e - 616 ∧ (g + 16 + 8 ≤ e - 616 - 4096 ∨ e - 616 ≤ g + 16) ∧
    (g + 16 ≤ e - 616 ∨ e - 616 + 16 ≤ g) := by omega

/-- A source range inside the input: below `2^48` and outside the callee's stack. -/
theorem src_call_facts {e p l src n : Nat} (he : 4800 ≤ e) (hp0 : p ≤ src) (hs : src + n ≤ p + l)
    (hpl : p + l ≤ 2 ^ 48) (hpw : p + l ≤ e - 4800 ∨ e + 40 ≤ p) :
    src + n ≤ 2 ^ 48 ∧ (src + n ≤ e - 616 - 4096 ∨ e - 616 ≤ src) ∧
    (src + n ≤ e - 616 + 8 ∨ e - 616 + 8 + 24 ≤ src) := by omega

theorem win_apart_out {e a n : Nat} (he : 4800 ≤ e) (h : a + n ≤ e - 4800 ∨ e - 4800 + (4800 + 40) ≤ a) :
    a + n ≤ e - 4800 ∨ e + 40 ≤ a := by omega

theorem bv_eq_false_of {x y : BitVec 64} (h : x.toNat ≠ y.toNat) : (x = y) = False := by
  simp only [eq_iff_iff, iff_false]; intro h'; exact h (congrArg _ h')

/-- The `JE` of `CMPQ x, y` (janus normal form) is false for different pointers below `2^64`. -/
theorem ptr_je_false {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    ((2 ^ 64 - b + a) % 2 ^ 64 = 0) = False := by
  simp only [eq_iff_iff, iff_false]; omega

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run

open Janus Janus.Contracts

/-- `RightPadBytes`' copy: a buffer of `size` bytes whose first `n = min size (ll - start)` bytes were copied from the
call data at `start` (via an intermediate memory `mW` that agrees with the call data there) and whose other bytes are
zero has the padded big-endian value of the call data. -/
theorem padded_val {mW m s0 : Janus.Arm64.Memory} {dst src n size pp ll start : Nat}
    (hcp : ∀ i, i < n → m.bytes (dst + i) = mW.bytes (src + i))
    (hsrcv : 0 < n → ∀ i, i < n → mW.readLE (src + i) 1 = s0.readLE (pp + (start + i)) 1)
    (hrest : ∀ i, n ≤ i → i < size → m.readLE (dst + i) 1 = 0)
    (hn : n = min size (ll - start)) :
    beVal m dst size = padBE s0 pp ll start size := by
  apply beVal_padded
  intro j hj
  unfold padByte
  by_cases hjn : j < n
  · rw [if_pos (by omega), hcp j hjn, ← Janus.Arm64.Memory.readLE_one, hsrcv (by omega) j hjn,
      Janus.Arm64.Memory.readLE_one]
  · rw [if_neg (by omega), ← Janus.Arm64.Memory.readLE_one, hrest j (by omega) hj]

/-- The frame of a fresh-buffer `memmove` call site, as a named closer (asm s84; `janus_frame` took 5-14 s per call
in the big contexts): one spill at `sp - k1` and the return-address push at `sp - 616` inside the window, then the
callee's frame (its stack and the destination `[d, d + n)`, a runtime object). -/
theorem frame_copy_fresh {rt : List (Nat × Nat)} {M m : Janus.Arm64.Memory} {sp k1 v1 v2 d n e : Nat}
    (hb : 4800 ≤ sp) (hk1 : 8 ≤ k1) (hk1' : k1 ≤ 4800) (hfe : d + n ≤ e) (hrt : InRanges d (e - d) rt)
    (hF : MemFrame ((M.writeLE (sp - k1) 8 v1).writeLE (sp - 616) 8 v2) m
      (rt ++ [(sp - 616 - 4096, sp - 616), (sp - 616 + 8, sp - 616 + 8 + 24)] ++ [(d, d + n)])) :
    MemFrame M m (rt ++ [(sp - 4800, sp + 40)]) := by
  refine MemFrame.trans (((MemFrame.refl M [(sp - 4800, sp + 40)]).writeLE v1 (List.mem_singleton_self _)
    (by omega) (by omega)).writeLE v2 (List.mem_singleton_self _) (by omega) (by omega)) hF ?_
  intro a k h
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  have hd := InRanges.apart (hrt.sub (n := n) (Nat.le_refl _) (by omega)) h.1
  unfold Apart at hd
  exact ⟨h.2, ⟨h.1, by omega, by omega⟩, by omega⟩

/-- A `w`-byte store at `sp - k` (`w ≤ k ≤ W`) inside the window `[sp - W, sp + 40)` keeps a window frame (asm s84:
named closers for the call-site `MemFrame` goals that `janus_frame` proved in 5-14 s each in the big contexts). -/
theorem frame_w {M M' : Janus.Arm64.Memory} {sp k w W : Nat} (v : Nat) (h : MemFrame M M' [(sp - W, sp + 40)])
    (hb : W ≤ sp) (hk : w ≤ k) (hk' : k ≤ W) : MemFrame M (M'.writeLE (sp - k) w v) [(sp - W, sp + 40)] :=
  h.writeLE v (List.mem_singleton_self _) (by omega) (by omega)

/-- Stores in the window, then a runtime call (its stack `[sp-616-4096, sp-616) ∪ [sp-608, sp-584)`): a frame of
`R.rt ++ window`. -/
theorem frame_cs_trans {rt : List (Nat × Nat)} {M M' m : Janus.Arm64.Memory} {sp W : Nat} (hW : 4800 ≤ W)
    (hb : W ≤ sp) (hM : MemFrame M M' [(sp - W, sp + 40)])
    (hF : MemFrame M' m (rt ++ [(sp - 616 - 4096, sp - 616), (sp - 616 + 8, sp - 616 + 8 + 24)])) :
    MemFrame M m (rt ++ [(sp - W, sp + 40)]) := by
  refine MemFrame.trans hM hF ?_
  intro a k h
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  exact ⟨h.2, h.1, by omega, by omega⟩

/-- `frame_cs_trans` with the callee also writing a stack buffer `[sp - k, sp - k + n)` of at most 32 bytes. -/
theorem frame_csb_trans {rt : List (Nat × Nat)} {M M' m : Janus.Arm64.Memory} {sp k n : Nat} (hb : 4800 ≤ sp)
    (hk : 8 ≤ k) (hk' : k ≤ 4800) (hn : n ≤ 32) (hM : MemFrame M M' [(sp - 4800, sp + 40)])
    (hF : MemFrame M' m (rt ++ [(sp - 616 - 4096, sp - 616), (sp - 616 + 8, sp - 616 + 8 + 24)] ++
      [(sp - k, sp - k + n)])) :
    MemFrame M m (rt ++ [(sp - 4800, sp + 40)]) := by
  refine MemFrame.trans hM hF ?_
  intro a k' h
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  exact ⟨h.2, ⟨h.1, by omega, by omega⟩, by omega⟩

/-- The input pointer plus its offset never wraps (a named run lemma: the failed `mod64_of_lt` discharges of
`(p + inOff len) % 2^64` cost 1-3.5 s each in the `DM` runs; asm s84). -/
theorem pin_mod {p l : Nat} (len : BitVec 64) (hp : p + l ≤ 2 ^ 48) :
    (p + inOff len) % 18446744073709551616 = p + inOff len := by
  unfold inOff; split <;> omega

end FvModexp.Amd64.Run
