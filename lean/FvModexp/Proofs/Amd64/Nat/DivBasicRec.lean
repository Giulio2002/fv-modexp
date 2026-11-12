import FvModexp.Proofs.Amd64.Nat.DivBasicRel
import FvModexp.Proofs.Amd64.Nat.DivBasicLay
import FvModexp.Proofs.Common.AsmDivVW

set_option autoImplicit false

/-!
# `divBasic` (amd64): after `stk.nat` — `vn1 := v[n-1]`, the INLINED `rec := reciprocalWord(vn1)`, `j := m`,
`ujn := 0`, to the loop head (natdiv.go:654-662)

Code `+0xb4 … +0x166` (`BSRQ`, `SHLQ`, `SBBQ`, `NOTQ`, `DIVQ`; `v` normalised ⇒ `nlz = 0`, no shift, no panic), then
`JMP head`. The twin of `Arm64/Nat/DivBasicRec.lean` (whose `reciprocalWord` is a call).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

/-- `Env` from `stk.nat`'s post (pure) -/
theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    (hpre : Pre R b L qp ql st up ul uc vp vl s) {S2 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hext : LiveExt R L L1) (hbud : b - stackNatCost (stLen s.mem st) (vl + 1) ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen s.mem st + (vl + 1 + 3) / 4 * 4)
    (hsame : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st → stW S2 st = stW s.mem st ∧ stCap S2 st = stCap s.mem st)
    (hgrow : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = s.mem.accessible a n v)
    (hmem : stCap s.mem st < stLen s.mem st + (vl + 1 + 3) / 4 * 4 → (stW S2 st, stW S2 st + 8 * stCap S2 st) ∈ L1)
    (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    Env R b L qp ql st up ul uc vp vl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have hscr := Scr.of_post (m0 := s.mem) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_, ?_, hx15, hdf, hra⟩
  · rw [← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + (vl + 1 + 3) / 4 * 4 ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hacc2]; exact a3, a4⟩
  · exact (ArrIn.of_nat (L1 := L1) (m0 := s.mem) (m := S2) hlc hlen hsame hmem :)

/-- `reciprocalWord` of a normalised word is `(2^128 - 1) / d - 2^64` (`nlz = 0`) -/
theorem recip_top (d : Nat) (h1 : 2 ^ 63 ≤ d) (h2 : d < 2 ^ 64) :
    AsmDiv.recipWord d = 340282366920938463463374607431768211455 / d - 18446744073709551616 := by
  have hn := FvModexp.AsmDiv.clz_norm64 d (by omega) h2
  have hc : Janus.Arm64.clzNat 64 d = 0 := by
    rcases Nat.eq_zero_or_pos (Janus.Arm64.clzNat 64 d) with h | h
    · exact h
    · exfalso
      have : d * 2 ≤ d * 2 ^ Janus.Arm64.clzNat 64 d := Nat.mul_le_mul_left _ (Nat.one_lt_two_pow_iff.2 (by omega))
      omega
  unfold AsmDiv.recipWord; rw [hc, Nat.pow_zero, Nat.mul_one]

/-- the memory at the head: `vn1`, `cap`, `len`, `ptr` of `qhatv`, `rec` stored -/
@[reducible] def recMem (M : Memory) (sp V vl t rc : Nat) : Memory :=
  ((((M.writeLE (sp - 72) 8 V).writeLE (sp - 64) 8 (vl + 1)).writeLE (sp - 120) 8 (vl + 1)).writeLE (sp - 56) 8 t).writeLE
    (sp - 136) 8 rc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the run `+0xb4 → head` on a small context (the inlined `reciprocalWord`) -/
theorem recRun (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (s S2 : State) (vp vl t V mm : Nat)
    (hsp0 : 4424 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 88 ≤ 2 ^ 48)
    (hpc2 : S2.rip = BitVec.ofNat 64 (callNat + 5)) (hsp2 : S2.regs 4 = s.regs 4 - 224#64)
    (hr0 : S2.regs 0 = BitVec.ofNat 64 t) (hr1 : S2.regs 1 = BitVec.ofNat 64 (vl + 1))
    (hr3 : S2.regs 3 = BitVec.ofNat 64 (vl + 1)) (hv2 : 2 ≤ vl) (hvb : vl + 4 ≤ 2 ^ 16) (ht : t < 2 ^ 64)
    (hv48 : vp + 8 * vl ≤ 2 ^ 48)
    (hwacc : S2.mem.accessible ((s.regs 4).toNat - 4424) (4424 + 88) true = true)
    (hvacc : S2.mem.accessible vp (8 * vl) false = true)
    (q16 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = vl) (q8 : S2.mem.readLE ((s.regs 4).toNat + 8) 8 = vp)
    (qn1 : S2.mem.readLE ((s.regs 4).toNat - 64) 8 = vl - 1)
    (qmm : S2.mem.readLE ((s.regs 4).toNat - 104) 8 = mm) (hmm : mm < 2 ^ 64)
    (hvn1 : S2.mem.readLE (vp + vl * 8 - 8) 8 = V) (hvtop : 2 ^ 63 ≤ V) (hV64 : V < 2 ^ 64)
    (k : ∀ S : State, S.rip = BitVec.ofNat 64 head → S.regs 4 = S2.regs 4 → S.regs 5 = S2.regs 5 →
      S.regs 14 = S2.regs 14 → S.fsBase = S2.fsBase → S.xmm 15 = S2.xmm 15 → S.df = S2.df →
      S.regs 0 = BitVec.ofNat 64 (AsmDiv.recipWord V) → S.regs 1 = BitVec.ofNat 64 vl →
      S.regs 2 = BitVec.ofNat 64 mm → S.regs 3 = BitVec.ofNat 64 (vl + 1) → S.regs 6 = BitVec.ofNat 64 vp →
      S.regs 7 = BitVec.ofNat 64 (vl + 1) → S.regs 8 = 0#64 → S.regs 10 = BitVec.ofNat 64 t →
      S.regs 11 = BitVec.ofNat 64 V →
      S.mem = recMem S2.mem (s.regs 4).toNat V vl t (AsmDiv.recipWord V) → ReachesRet (LibDivBasic.program.link impl) r S Q) :
    ReachesRet (LibDivBasic.program.link impl) r S2 Q := by
  have hrv0 := FvModexp.AsmDivVW.recip_val _ hvtop hV64
  have hrw := recip_top V hvtop hV64
  have hrl0 : 340282366920938463463374607431768211455 / V - 18446744073709551616 < 18446744073709551616 :=
    FvModexp.AsmDivVW.recip_lt _ hvtop
  have hy0 : (V = 0) = False := by simp; omega
  have hVm : V % 18446744073709551616 = V := Nat.mod_eq_of_lt hV64
  have hc : Janus.Arm64.clzNat 64 V = 0 := by
    have hn := FvModexp.AsmDiv.clz_norm64 V (by omega) hV64
    rcases Nat.eq_zero_or_pos (Janus.Arm64.clzNat 64 V) with h | h
    · exact h
    · exfalso
      have : V * 2 ≤ V * 2 ^ Janus.Arm64.clzNat 64 V := Nat.mul_le_mul_left _ (Nat.one_lt_two_pow_iff.2 (by omega))
      omega
  have hA' : ∀ x : BitVec 64, x &&& 18446744073709551615#64 = x := fun x => by
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
  janus64_run [hr0, hr1, hr3, q16, q8, qn1, qmm, hvn1, hy0, hVm, hc, hA', BitVec.toNat_not, hrv0] until [head]
  refine k _ ?pc ?_ ?_ ?_ rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?mem
  case pc => janus64_simp
  case mem => simp only [recMem, hrw]
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hrw, hr3]

end FvModexp.Amd64.DivBasic
