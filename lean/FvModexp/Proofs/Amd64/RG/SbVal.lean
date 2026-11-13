import FvModexp.Proofs.Common.Util

set_option autoImplicit false

/-! `(*uint256.Int).SetBytes` (amd64): the value closers of the per-length cases (`RG/Sb{A..G}`) as a few generic lemmas
(agent infra s53). A case's post-run value goal is `w₀ + 2^64·w₁ + … + 2^(64k)·H = fromBE bytes n` with each `wⱼ` a
byte-reversed 8-byte load and `H` the length-`n % 8` head in one of the nine compiled shapes; closing it with one `exact`
of `as1`/`as2`/`as3` + a head lemma gives a small kernel term (the per-case `simp`/`omega` closer was ~9 s of kernel
checking per case). -/

namespace FvModexp.Amd64.RG.SbVal

open Janus.Arm64

theorem word (m : Memory) (a : Nat) : Janus.Arm64.revBytesNat 8 (m.readLE a 8) % 18446744073709551616 = Aux.fromBE (fun i => m.readLE (a + i) 1) 8 := by
  have h := Util.revBytes_lt 8 (m.readLE a 8)
  simp only [Nat.reducePow] at h
  rw [Nat.mod_eq_of_lt h]
  exact Util.revBytes_readLE m a 8

theorem split8 (m : Memory) (p h : Nat) :
    Aux.fromBE (fun i => m.readLE (p + i) 1) (h + 8) =
      Aux.fromBE (fun i => m.readLE (p + i) 1) h * 18446744073709551616 + Aux.fromBE (fun i => m.readLE (p + h + i) 1) 8 := by
  rw [Util.fromBE_add]
  simp only [Nat.add_assoc, Nat.reducePow]

/-- one word below the head -/
theorem as1 (m : Memory) (p h n a H : Nat) (hH : H = Aux.fromBE (fun i => m.readLE (p + i) 1) h) (ha : a = p + h) (hn : h + 8 = n) :
    Janus.Arm64.revBytesNat 8 (m.readLE a 8) % 18446744073709551616 + 18446744073709551616 * H = Aux.fromBE (fun i => m.readLE (p + i) 1) n := by
  subst hn ha hH
  rw [split8, ← word]
  omega

/-- two words below the head -/
theorem as2 (m : Memory) (p h n a b H : Nat) (hH : H = Aux.fromBE (fun i => m.readLE (p + i) 1) h) (ha : a = p + h + 8) (hb : b = p + h) (hn : h + 16 = n) :
    Janus.Arm64.revBytesNat 8 (m.readLE a 8) % 18446744073709551616 + 18446744073709551616 * (Janus.Arm64.revBytesNat 8 (m.readLE b 8) % 18446744073709551616) + 340282366920938463463374607431768211456 * H = Aux.fromBE (fun i => m.readLE (p + i) 1) n := by
  subst hn
  have e1 := as1 m p h (h + 8) b H hH hb rfl
  have e2 := split8 m p (h + 8)
  have e3 := word m (p + (h + 8))
  rw [show p + (h + 8) = a by omega] at e2 e3
  rw [show h + 16 = h + 8 + 8 by omega]
  omega

/-- three words below the head -/
theorem as3 (m : Memory) (p h n a b c H : Nat) (hH : H = Aux.fromBE (fun i => m.readLE (p + i) 1) h) (ha : a = p + h + 16) (hb : b = p + h + 8) (hc : c = p + h)
    (hn : h + 24 = n) :
    Janus.Arm64.revBytesNat 8 (m.readLE a 8) % 18446744073709551616 + 18446744073709551616 * (Janus.Arm64.revBytesNat 8 (m.readLE b 8) % 18446744073709551616) + 340282366920938463463374607431768211456 * (Janus.Arm64.revBytesNat 8 (m.readLE c 8) % 18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 * H = Aux.fromBE (fun i => m.readLE (p + i) 1) n := by
  subst hn
  have e1 := as2 m p h (h + 16) b c H hH hb hc rfl
  have e2 := split8 m p (h + 16)
  have e3 := word m (p + (h + 16))
  rw [show p + (h + 16) = a by omega] at e2 e3
  rw [show h + 24 = h + 16 + 8 by omega]
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd1 (m : Memory) (p : Nat) :
    Janus.Arm64.Memory.readLE m p 1 % 4294967296 = Aux.fromBE (fun i => m.readLE (p + i) 1) 1 := by
  have := Util.rd1_lt m p; have := Util.rd2_lt m p; have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd2 (m : Memory) (p : Nat) :
    BitVec.toNat (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 (Janus.Arm64.Memory.readLE m p 2))) &&& 18446744073709486080#64 ||| BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 (Janus.Arm64.Memory.readLE m p 2))))).rotateLeft 8)) % 65536 % 4294967296 = Aux.fromBE (fun i => m.readLE (p + i) 1) 2 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd2_lt m p; have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd3 (m : Memory) (p : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m p 1))) <<< (16 : Nat) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 (Janus.Arm64.Memory.readLE m (p + 1) 2))) &&& 18446744073709486080#64 ||| BitVec.setWidth 64 ((BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 (Janus.Arm64.Memory.readLE m (p + 1) 2))))).rotateLeft 8))))).toNat = Aux.fromBE (fun i => m.readLE (p + i) 1) 3 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd4 (m : Memory) (p : Nat) :
    Janus.Arm64.revBytesNat 4 (Janus.Arm64.Memory.readLE m p 4 % 4294967296) % 4294967296 = Aux.fromBE (fun i => m.readLE (p + i) 1) 4 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd1_lt m (p + 3); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have := Util.rd2_lt m (p + 2); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); have h2b2 : m.readLE (p + 2) 2 = m.readLE (p + 2) 1 + 256 * m.readLE (p + 3) 1 := Util.rd2_bytes m (p + 2); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd5 (m : Memory) (p : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m p 1))) <<< (32 : Nat) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (Janus.Arm64.revBytesNat 4 (Janus.Arm64.Memory.readLE m (p + 1) 4 % 4294967296)))))).toNat = Aux.fromBE (fun i => m.readLE (p + i) 1) 5 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd1_lt m (p + 3); have := Util.rd1_lt m (p + 4); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have := Util.rd2_lt m (p + 2); have := Util.rd2_lt m (p + 3); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); have h2b2 : m.readLE (p + 2) 2 = m.readLE (p + 2) 1 + 256 * m.readLE (p + 3) 1 := Util.rd2_bytes m (p + 2); have h2b3 : m.readLE (p + 3) 2 = m.readLE (p + 3) 1 + 256 * m.readLE (p + 4) 1 := Util.rd2_bytes m (p + 3); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd6 (m : Memory) (p : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m p 1))) <<< (40 : Nat) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m (p + 1) 1))) <<< (32 : Nat) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (Janus.Arm64.revBytesNat 4 (Janus.Arm64.Memory.readLE m (p + 2) 4 % 4294967296))))))).toNat = Aux.fromBE (fun i => m.readLE (p + i) 1) 6 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd1_lt m (p + 3); have := Util.rd1_lt m (p + 4); have := Util.rd1_lt m (p + 5); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have := Util.rd2_lt m (p + 2); have := Util.rd2_lt m (p + 3); have := Util.rd2_lt m (p + 4); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); have h2b2 : m.readLE (p + 2) 2 = m.readLE (p + 2) 1 + 256 * m.readLE (p + 3) 1 := Util.rd2_bytes m (p + 2); have h2b3 : m.readLE (p + 3) 2 = m.readLE (p + 3) 1 + 256 * m.readLE (p + 4) 1 := Util.rd2_bytes m (p + 3); have h2b4 : m.readLE (p + 4) 2 = m.readLE (p + 4) 1 + 256 * m.readLE (p + 5) 1 := Util.rd2_bytes m (p + 4); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd7 (m : Memory) (p : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m p 1))) <<< (48 : Nat) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m (p + 1) 1))) <<< (40 : Nat) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m (p + 2) 1))) <<< (32 : Nat) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (Janus.Arm64.revBytesNat 4 (Janus.Arm64.Memory.readLE m (p + 3) 4 % 4294967296)))))))).toNat = Aux.fromBE (fun i => m.readLE (p + i) 1) 7 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd1_lt m (p + 3); have := Util.rd1_lt m (p + 4); have := Util.rd1_lt m (p + 5); have := Util.rd1_lt m (p + 6); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have := Util.rd2_lt m (p + 2); have := Util.rd2_lt m (p + 3); have := Util.rd2_lt m (p + 4); have := Util.rd2_lt m (p + 5); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); have h2b2 : m.readLE (p + 2) 2 = m.readLE (p + 2) 1 + 256 * m.readLE (p + 3) 1 := Util.rd2_bytes m (p + 2); have h2b3 : m.readLE (p + 3) 2 = m.readLE (p + 3) 1 + 256 * m.readLE (p + 4) 1 := Util.rd2_bytes m (p + 3); have h2b4 : m.readLE (p + 4) 2 = m.readLE (p + 4) 1 + 256 * m.readLE (p + 5) 1 := Util.rd2_bytes m (p + 4); have h2b5 : m.readLE (p + 5) 2 = m.readLE (p + 5) 1 + 256 * m.readLE (p + 6) 1 := Util.rd2_bytes m (p + 5); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd6b (m : Memory) (p : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m p 1))) <<< (40 : Nat) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (Janus.Arm64.revBytesNat 4 (Janus.Arm64.Memory.readLE m (p + 2) 4 % 4294967296))))) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m (p + 1) 1))) <<< (32 : Nat))).toNat = Aux.fromBE (fun i => m.readLE (p + i) 1) 6 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd1_lt m (p + 3); have := Util.rd1_lt m (p + 4); have := Util.rd1_lt m (p + 5); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have := Util.rd2_lt m (p + 2); have := Util.rd2_lt m (p + 3); have := Util.rd2_lt m (p + 4); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); have h2b2 : m.readLE (p + 2) 2 = m.readLE (p + 2) 1 + 256 * m.readLE (p + 3) 1 := Util.rd2_bytes m (p + 2); have h2b3 : m.readLE (p + 3) 2 = m.readLE (p + 3) 1 + 256 * m.readLE (p + 4) 1 := Util.rd2_bytes m (p + 3); have h2b4 : m.readLE (p + 4) 2 = m.readLE (p + 4) 1 + 256 * m.readLE (p + 5) 1 := Util.rd2_bytes m (p + 4); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
theorem hd7b (m : Memory) (p : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m p 1))) <<< (48 : Nat) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m (p + 1) 1))) <<< (40 : Nat) ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (Janus.Arm64.revBytesNat 4 (Janus.Arm64.Memory.readLE m (p + 3) 4 % 4294967296))))) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (Janus.Arm64.Memory.readLE m (p + 2) 1))) <<< (32 : Nat)))).toNat = Aux.fromBE (fun i => m.readLE (p + i) 1) 7 := by
  have := Util.rd1_lt m p; have := Util.rd1_lt m (p + 1); have := Util.rd1_lt m (p + 2); have := Util.rd1_lt m (p + 3); have := Util.rd1_lt m (p + 4); have := Util.rd1_lt m (p + 5); have := Util.rd1_lt m (p + 6); have := Util.rd2_lt m p; have := Util.rd2_lt m (p + 1); have := Util.rd2_lt m (p + 2); have := Util.rd2_lt m (p + 3); have := Util.rd2_lt m (p + 4); have := Util.rd2_lt m (p + 5); have h2b0 : m.readLE p 2 = m.readLE p 1 + 256 * m.readLE (p + 1) 1 := Util.rd2_bytes m p; have h2b1 : m.readLE (p + 1) 2 = m.readLE (p + 1) 1 + 256 * m.readLE (p + 2) 1 := Util.rd2_bytes m (p + 1); have h2b2 : m.readLE (p + 2) 2 = m.readLE (p + 2) 1 + 256 * m.readLE (p + 3) 1 := Util.rd2_bytes m (p + 2); have h2b3 : m.readLE (p + 3) 2 = m.readLE (p + 3) 1 + 256 * m.readLE (p + 4) 1 := Util.rd2_bytes m (p + 3); have h2b4 : m.readLE (p + 4) 2 = m.readLE (p + 4) 1 + 256 * m.readLE (p + 5) 1 := Util.rd2_bytes m (p + 4); have h2b5 : m.readLE (p + 5) 2 = m.readLE (p + 5) 1 + 256 * m.readLE (p + 6) 1 := Util.rd2_bytes m (p + 5); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Aux.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))

end FvModexp.Amd64.RG.SbVal
