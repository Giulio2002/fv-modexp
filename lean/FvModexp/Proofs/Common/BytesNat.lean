import FvModexp.Proofs.Common.DivContract
/-!
# Byte conversions, bit length, `low64` and the `stack` allocator (nat.go, int.go)

Byte buffers (`[]byte`) are `List Nat` in Go index order (`buf[0]` first = most significant byte for big-endian encodings);
every byte is `< 256` (`Bt buf`).  `beVal buf` is the big-endian value.

Go sources (go-bigmodexpfix @f9e208c548ab `src/math/big`, and Go 1.26.10 `math/big`, whose `setBytes` is identical):
* `setBytes`     nat.go:1665-1685 (fork) = go1.26.10 math/big/nat.go:1022-1040 (`nat.setBytes`, used by `Int.SetBytes`)
* `bigEndianWord` nat.go:1656-1661 (`byteorder.BEUint64`)
* `natBytes`     nat.go:1627-1653 (`(z nat) bytes(buf)`);   `intBytes` int.go:527-533 (`(*Int).Bytes`)
* `natBitLen`    nat.go:342-360 (fork) = go1.26.10 nat.go:332-350;  `Int.BitLen` int.go:548-553
* `low64`        int.go:416-425;  `Int.Uint64` int.go:439-441;  `Int.IsUint64` int.go:453-455;  `Int.SetBytes` int.go:518-522
* `stackNatRound` nat.go:319-329 (`(*stack).nat`: `nr := (n + 3) &^ 3`)
-/
namespace FvModexp.Mdl

/-- All entries are bytes. -/
def Bt (l : List Nat) : Prop := ∀ b ∈ l, b < 256

/-- Big-endian value of a byte list. -/
def beVal (l : List Nat) : Nat := l.foldl (fun a b => a * 256 + b) 0

theorem foldl_be_acc (l : List Nat) (acc : Nat) :
    l.foldl (fun a b => a * 256 + b) acc = acc * 256 ^ l.length + l.foldl (fun a b => a * 256 + b) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + b), Nat.pow_succ]
    grind

theorem beVal_append (a b : List Nat) : beVal (a ++ b) = beVal a * 256 ^ b.length + beVal b := by
  unfold beVal; rw [List.foldl_append, foldl_be_acc]

@[simp] theorem beVal_nil : beVal [] = 0 := rfl
theorem beVal_singleton (b : Nat) : beVal [b] = b := by simp [beVal]

theorem getD_lt (l : List Nat) (i : Nat) (h : i < l.length) : l.getD i 0 = l[i] := by simp [h]

theorem beVal_cons (b : Nat) (l : List Nat) : beVal (b :: l) = b * 256 ^ l.length + beVal l := by
  rw [show b :: l = [b] ++ l from rfl, beVal_append, beVal_singleton]

theorem beVal_lt {l : List Nat} (h : Bt l) : beVal l < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    rw [beVal_cons, List.length_cons, Nat.pow_succ]
    have hb : b < 256 := h b (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    have : b * 256 ^ bs.length + 256 ^ bs.length ≤ 256 ^ bs.length * 256 := by
      have := Nat.mul_le_mul_right (256 ^ bs.length) (show b + 1 ≤ 256 by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 256] at this; exact this
    omega

theorem Bt_append {a b : List Nat} : Bt (a ++ b) ↔ Bt a ∧ Bt b := by
  unfold Bt; simp only [List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩, fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x)⟩
theorem Bt.take {l : List Nat} (h : Bt l) (n : Nat) : Bt (l.take n) := fun b hb => h b (List.mem_of_mem_take hb)
theorem Bt.drop {l : List Nat} (h : Bt l) (n : Nat) : Bt (l.drop n) := fun b hb => h b (List.mem_of_mem_drop hb)

/-! ## setBytes -/

/-- `bigEndianWord(b)` = `byteorder.BEUint64(b)` (nat.go:1656) on an 8-byte slice. -/
def bigEndianWord (b : List Nat) : Nat := beVal b

/-- The loop `for k := 0; i >= _S; k++ { z[k] = bigEndianWord(buf[i-_S : i]); i -= _S }` (nat.go:1669-1672), returning the
words `z[0], z[1], …` in order and the final `i`.  `fuel` bounds the iterations (any `fuel ≥ i / 8` is exact). -/
def sbWords (buf : List Nat) : Nat → Nat → List Nat × Nat
  | 0, i => ([], i)
  | f + 1, i =>
    if 8 ≤ i then
      let r := sbWords buf f (i - 8)
      (bigEndianWord ((buf.drop (i - 8)).take 8) :: r.1, r.2)
    else ([], i)

/-- The loop `for s := uint(0); i > 0; s += 8 { d |= Word(buf[i-1]) << s; i-- }` (nat.go:1675-1678). -/
def sbTail (buf : List Nat) : Nat → Nat → Nat → Nat
  | 0, _, d => d
  | i + 1, s, d => sbTail buf i (s + 8) (d ||| (buf.getD i 0 * 2 ^ s % 2 ^ 64))

/-- nat.go:1665 `(z nat) setBytes(buf []byte) nat`: `z.make((len(buf)+7)/8)`, the word loop, the partial top word
`z[len(z)-1] = d` when `i > 0`, then `z.norm()`. -/
def natSetBytes (buf : List Nat) : List Nat :=
  let r := sbWords buf buf.length buf.length
  norm (if 0 < r.2 then r.1 ++ [sbTail buf r.2 0 0] else r.1)

theorem sbTail_spec (buf : List Nat) (hb : Bt buf) :
    ∀ (j s d : Nat), j ≤ buf.length → s + 8 * j ≤ 64 → d < 2 ^ s →
      sbTail buf j s d = d + 2 ^ s * beVal (buf.take j)
  | 0, s, d, _, _, _ => by simp [sbTail]
  | j + 1, s, d, hj, hs, hd => by
    have hbj : buf.getD j 0 < 256 := by
      rw [getD_lt _ _ (by omega)]; exact hb _ (List.getElem_mem _)
    have hlt : buf.getD j 0 * 2 ^ s < 2 ^ 64 := by
      have : buf.getD j 0 * 2 ^ s < 2 ^ 8 * 2 ^ s := Nat.mul_lt_mul_of_pos_right (by simpa using hbj) (Nat.two_pow_pos _)
      have e : 2 ^ 8 * 2 ^ s ≤ 2 ^ 64 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hor : d ||| (buf.getD j 0 * 2 ^ s % 2 ^ 64) = d + 2 ^ s * buf.getD j 0 := by
      rw [Nat.mod_eq_of_lt hlt, Nat.mul_comm, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hd, Nat.add_comm]
    have hd' : d + 2 ^ s * buf.getD j 0 < 2 ^ (s + 8) := by
      rw [Nat.pow_add]
      have := Nat.mul_le_mul_left (2 ^ s) (show buf.getD j 0 + 1 ≤ 2 ^ 8 from hbj)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    simp only [sbTail]
    rw [hor, sbTail_spec buf hb j (s + 8) _ (by omega) (by omega) hd']
    have htk : buf.take (j + 1) = buf.take j ++ [buf.getD j 0] := by
      rw [getD_lt _ _ (by omega), List.take_succ_eq_append_getElem (by omega)]
    rw [htk, beVal_append, beVal_singleton, Nat.pow_add]
    simp only [List.length_singleton, Nat.pow_one]
    grind

theorem pow64_eq (k : Nat) : (2 : Nat) ^ (64 * k) = 256 ^ (8 * k) := by
  rw [Nat.pow_mul, Nat.pow_mul]

theorem sbWords_spec (buf : List Nat) (hb : Bt buf) :
    ∀ (f i : Nat), i ≤ buf.length → i / 8 ≤ f →
      (sbWords buf f i).2 = i % 8 ∧ (sbWords buf f i).1.length = i / 8 ∧ Wd (sbWords buf f i).1 ∧
      beVal (buf.take i) = beVal (buf.take (i % 8)) * 2 ^ (64 * (i / 8)) + val (sbWords buf f i).1
  | 0, i, hi, hf => by
    have : i < 8 := by omega
    simp [sbWords, Nat.mod_eq_of_lt this, Nat.div_eq_of_lt this, Wd_nil]
  | f + 1, i, hi, hf => by
    by_cases h8 : 8 ≤ i
    · simp only [sbWords, h8, ite_true]
      obtain ⟨r1, r2, r3, r4⟩ := sbWords_spec buf hb f (i - 8) (by omega) (by omega)
      have hm : (i - 8) % 8 = i % 8 := by omega
      have hk : (i - 8) / 8 + 1 = i / 8 := by omega
      rw [hm] at r1 r4
      have hseg : ((buf.drop (i - 8)).take 8).length = 8 := by simp; omega
      have hsegB : Bt ((buf.drop (i - 8)).take 8) := (hb.drop _).take _
      have hw : bigEndianWord ((buf.drop (i - 8)).take 8) < 2 ^ 64 := by
        have := beVal_lt hsegB; rw [hseg] at this; unfold bigEndianWord; simpa using this
      refine ⟨r1, by simp [r2]; omega, Wd_cons.2 ⟨hw, r3⟩, ?_⟩
      have htk : buf.take i = buf.take (i - 8) ++ (buf.drop (i - 8)).take 8 := by
        have : i = (i - 8) + 8 := by omega
        conv => lhs; rw [this]
        rw [List.take_add]
      rw [htk, beVal_append, hseg, r4, val_cons, ← hk]
      unfold bigEndianWord
      have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [e, Nat.mul_add, Nat.mul_one, Nat.pow_add]
      generalize beVal ((buf.drop (i - 8)).take 8) = W
      generalize val (sbWords buf f (i - 8)).1 = V
      generalize beVal (buf.take (i % 8)) = T
      generalize (2 : Nat) ^ (64 * ((i - 8) / 8)) = P
      grind
    · have : i < 8 := by omega
      simp [sbWords, h8, Nat.mod_eq_of_lt this, Nat.div_eq_of_lt this, Wd_nil]

theorem natSetBytes_spec (buf : List Nat) (hb : Bt buf) :
    Wd (natSetBytes buf) ∧ Normed (natSetBytes buf) ∧ val (natSetBytes buf) = beVal buf ∧
    (natSetBytes buf).length ≤ (buf.length + 7) / 8 := by
  obtain ⟨r1, r2, r3, r4⟩ := sbWords_spec buf hb buf.length buf.length (Nat.le_refl _) (Nat.div_le_self _ _)
  rw [List.take_length] at r4
  unfold natSetBytes
  simp only []
  by_cases h0 : 0 < (sbWords buf buf.length buf.length).2
  · rw [if_pos h0]
    have hT := sbTail_spec buf hb (sbWords buf buf.length buf.length).2 0 0 (by omega) (by omega) (by decide)
    rw [r1] at hT ⊢
    have hTB : beVal (buf.take (buf.length % 8)) < 256 ^ (buf.length % 8) := by
      have := beVal_lt (hb.take (buf.length % 8)); simpa [List.length_take, Nat.min_eq_left (Nat.mod_le _ _)] using this
    have hTB' : beVal (buf.take (buf.length % 8)) < 2 ^ 64 := by
      have : 256 ^ (buf.length % 8) ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      have e : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
      omega
    simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hT
    refine ⟨Wd_norm (Wd_append.2 ⟨r3, Wd_cons.2 ⟨by rw [hT]; exact hTB', Wd_nil⟩⟩), normed_norm _, ?_, ?_⟩
    · rw [val_norm, val_append, hT, r4, r2]
      simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
      grind
    · refine Nat.le_trans (length_norm_le _) ?_
      simp [r2]; omega
  · rw [if_neg h0]
    have hm : buf.length % 8 = 0 := by omega
    refine ⟨Wd_norm r3, normed_norm _, ?_, Nat.le_trans (length_norm_le _) (by rw [r2]; omega)⟩
    rw [val_norm, r4, hm]; simp

/-! ## bytes / Int.Bytes -/

/-- Inner loop of `nat.bytes` (nat.go:1633-1641) for one word `d`:
`for j := 0; j < _S; j++ { i--; if i >= 0 { buf[i] = byte(d) } else if byte(d) != 0 { panic(...) }; d >>= 8 }`.
The panic branch is not modelled (theorems assume a large enough buffer). -/
def bytesWord : Nat → Nat → Int → List Nat → List Nat × Int
  | 0, _, i, buf => (buf, i)
  | j + 1, d, i, buf =>
    let i' := i - 1
    let buf' := if 0 ≤ i' then buf.set i'.toNat (d % 256) else buf
    bytesWord j (d / 256) i' buf'

/-- Outer loop `for _, d := range z { ... }` of `nat.bytes`. -/
def bytesLoop : List Nat → Int → List Nat → List Nat × Int
  | [], i, buf => (buf, i)
  | d :: ds, i, buf => let r := bytesWord 8 d i buf; bytesLoop ds r.2 r.1

/-- Number of leading zero bytes: the loop `for i < len(buf) && buf[i] == 0 { i++ }` counted from its start. -/
def lzBytes : List Nat → Nat
  | [] => 0
  | b :: bs => if b = 0 then lzBytes bs + 1 else 0

/-- nat.go:1628 `(z nat) bytes(buf []byte) (i int)`: returns the new buffer contents and `i`. -/
def natBytes (z buf : List Nat) : List Nat × Nat :=
  let r := bytesLoop z buf.length buf
  let i := if r.2 < 0 then 0 else r.2.toNat
  (r.1, i + lzBytes (r.1.drop i))

/-- int.go:527 `(*Int).Bytes()`: `buf := make([]byte, len(x.abs)*_S); return buf[x.abs.bytes(buf):]`. -/
def intBytes (abs : List Nat) : List Nat :=
  let r := natBytes abs (List.replicate (8 * abs.length) 0)
  r.1.drop r.2

/-- Big-endian `j`-byte encoding of `d mod 256^j`. -/
def beN : Nat → Nat → List Nat
  | 0, _ => []
  | j + 1, d => beN j (d / 256) ++ [d % 256]

/-- Big-endian encoding of a limb list, 8 bytes per limb (most significant limb first). -/
def beWords : List Nat → List Nat
  | [] => []
  | d :: ds => beWords ds ++ beN 8 d

theorem length_beN (j d : Nat) : (beN j d).length = j := by
  induction j generalizing d with
  | zero => rfl
  | succ j ih => simp [beN, ih]

theorem Bt_beN (j d : Nat) : Bt (beN j d) := by
  induction j generalizing d with
  | zero => intro b hb; simp [beN] at hb
  | succ j ih => exact Bt_append.2 ⟨ih _, by intro b hb; simp at hb; subst hb; exact Nat.mod_lt _ (by decide)⟩

theorem beVal_beN (j d : Nat) : beVal (beN j d) = d % 256 ^ j := by
  induction j generalizing d with
  | zero => simp [beN]; omega
  | succ j ih =>
    simp only [beN]
    rw [beVal_append, ih, beVal_singleton, List.length_singleton, Nat.pow_one, Nat.pow_succ, Nat.mul_comm (256 ^ j) 256,
      Nat.mod_mul]
    omega

theorem length_beWords (z : List Nat) : (beWords z).length = 8 * z.length := by
  induction z with
  | nil => rfl
  | cons d ds ih => simp [beWords, ih, length_beN]; omega

theorem Bt_beWords (z : List Nat) : Bt (beWords z) := by
  induction z with
  | nil => intro b hb; simp [beWords] at hb
  | cons d ds ih => exact Bt_append.2 ⟨ih, Bt_beN _ _⟩

theorem beVal_beWords {z : List Nat} (hz : Wd z) : beVal (beWords z) = val z := by
  induction z with
  | nil => rfl
  | cons d ds ih =>
    simp only [beWords]
    rw [beVal_append, ih hz.tail, beVal_beN, length_beN, val_cons, Nat.mod_eq_of_lt (by simpa using (Wd_cons.1 hz).1)]
    simp only [Nat.reducePow]; omega

theorem bytesWord_spec : ∀ (j d k : Nat) (buf : List Nat), j ≤ k → k ≤ buf.length →
    bytesWord j d (k : Int) buf = (buf.take (k - j) ++ beN j d ++ buf.drop k, ((k - j : Nat) : Int))
  | 0, d, k, buf, _, _ => by simp [bytesWord, beN]
  | j + 1, d, k, buf, hj, hk => by
    simp only [bytesWord]
    have e : (k : Int) - 1 = ((k - 1 : Nat) : Int) := by omega
    rw [e, if_pos (by omega), Int.toNat_natCast, bytesWord_spec j (d / 256) (k - 1) _ (by omega) (by simp; omega)]
    have e2 : k - 1 - j = k - (j + 1) := by omega
    rw [e2]
    simp only [Prod.mk.injEq, and_true]
    have h1 : (buf.set (k - 1) (d % 256)).take (k - (j + 1)) = buf.take (k - (j + 1)) := by
      rw [List.take_set, List.set_eq_of_length_le]; simp; omega
    have h2 : (buf.set (k - 1) (d % 256)).drop (k - 1) = (d % 256) :: buf.drop k := by
      rw [List.drop_set, if_neg (by omega), Nat.sub_self]
      have : buf.drop (k - 1) = buf[k - 1]'(by omega) :: buf.drop k := by
        rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
      rw [this]; rfl
    rw [h1, h2]; simp [beN]

theorem bytesLoop_spec : ∀ (z : List Nat) (k : Nat) (buf : List Nat), 8 * z.length ≤ k → k ≤ buf.length →
    bytesLoop z (k : Int) buf = (buf.take (k - 8 * z.length) ++ beWords z ++ buf.drop k, ((k - 8 * z.length : Nat) : Int))
  | [], k, buf, _, _ => by simp [bytesLoop, beWords]
  | d :: ds, k, buf, hz, hk => by
    simp only [bytesLoop]
    simp only [List.length_cons] at hz
    rw [bytesWord_spec 8 d k buf (by omega) hk]
    simp only []
    rw [bytesLoop_spec ds (k - 8) _ (by omega) (by simp [length_beN]; omega)]
    have e : k - 8 - 8 * ds.length = k - 8 * (ds.length + 1) := by omega
    simp only [List.length_cons, e, Prod.mk.injEq, and_true]
    have hl : (buf.take (k - 8)).length = k - 8 := by simp; omega
    rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
    rw [List.take_take, Nat.min_eq_left (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]
    simp [beWords]

theorem lzBytes_split (l : List Nat) : l = List.replicate (lzBytes l) 0 ++ l.drop (lzBytes l) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [lzBytes]
    split
    · rename_i h; subst h
      simp only [List.replicate_succ, List.cons_append, List.drop_succ_cons]
      exact congrArg _ ih
    · simp

theorem beVal_replicate_zero (k : Nat) (m : List Nat) : beVal (List.replicate k 0 ++ m) = beVal m := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, beVal_cons, ih]; simp

theorem lzBytes_head (l : List Nat) : ∀ b ∈ (l.drop (lzBytes l)).head?, b ≠ 0 := by
  induction l with
  | nil => simp [lzBytes]
  | cons b bs ih =>
    simp only [lzBytes]
    split
    · simpa using ih
    · rename_i h; simpa using h

theorem lzBytes_le (l : List Nat) : lzBytes l ≤ l.length := by
  induction l with
  | nil => simp [lzBytes]
  | cons b bs ih => simp only [lzBytes]; split <;> simp <;> omega

/-- `nat.bytes` into a buffer of exactly `8*len(z)` bytes (the `Int.Bytes` case): the buffer becomes the big-endian
encoding of `z` and `i` is the number of leading zero bytes. -/
theorem natBytes_exact (z buf : List Nat) (hl : buf.length = 8 * z.length) :
    natBytes z buf = (beWords z, lzBytes (beWords z)) := by
  unfold natBytes
  rw [hl, bytesLoop_spec z (8 * z.length) buf (Nat.le_refl _) (by omega)]
  simp [Nat.sub_self, List.drop_eq_nil_of_le (show buf.length ≤ 8 * z.length by omega)]

/-- `(*Int).Bytes()` returns the minimal big-endian encoding of `|x|`. -/
theorem intBytes_spec (abs : List Nat) (hw : Wd abs) :
    Bt (intBytes abs) ∧ beVal (intBytes abs) = val abs ∧ (∀ b ∈ (intBytes abs).head?, b ≠ 0) ∧
    intBytes abs = (beWords abs).drop (lzBytes (beWords abs)) := by
  have he : intBytes abs = (beWords abs).drop (lzBytes (beWords abs)) := by
    unfold intBytes; rw [natBytes_exact abs _ (by simp)]
  rw [he]
  refine ⟨(Bt_beWords abs).drop _, ?_, lzBytes_head _, rfl⟩
  rw [← beVal_beWords hw]
  conv => rhs; rw [lzBytes_split (beWords abs)]
  rw [beVal_replicate_zero]

end FvModexp.Mdl
