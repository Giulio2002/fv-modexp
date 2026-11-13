import FvModexp.Proofs.Amd64.NatQ.BasicSqrStep

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/BasicSqrEnv.lean — TIGHT COSTS, divmc s37] `basicSqr` (amd64): `Env` from `(*stack).nat`'s postcondition (pure; the amd64 twin of `Arm64/Nat/BasicSqrEnv.lean`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.BasicSqr

variable {H : Nat}

theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    (hpre : Pre R b H L st zp zl zc xp xl s) (hbig : 12 ≤ xl) {P S2 : Memory}
    (hPs : ∀ k, k + 8 ≤ 24 → P.readLE (st + k) 8 = s.mem.readLE (st + k) 8)
    (hPacc : ∀ a n v, P.accessible a n v = s.mem.accessible a n v)
    {L1 : List (Nat × Nat)} {b1 : Nat} (hext : LiveExt R L L1)
    (hbud : b - stkR H P st + stkR H S2 st ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen P st + (2 * xl + 3) / 4 * 4)
    (hsame : stLen P st + (2 * xl + 3) / 4 * 4 ≤ stCap P st → stW S2 st = stW P st ∧ stCap S2 st = stCap P st)
    (hgrow : stCap P st < stLen P st + (2 * xl + 3) / 4 * 4 → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = P.accessible a n v)
    (hmem : stCap P st < stLen P st + (2 * xl + 3) / 4 * 4 → (stW S2 st, stW S2 st + 8 * stCap S2 st) ∈ L1)
    (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    Env R b H L st zp zl zc xp xl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have eW : stW P st = stW s.mem st := hPs 0 (by omega)
  have eL : stLen P st = stLen s.mem st := hPs 8 (by omega)
  have eC : stCap P st = stCap s.mem st := hPs 16 (by omega)
  rw [eW, eL, eC] at hsame
  rw [eL, eC] at hgrow hmem
  rw [eL] at hlen
  rw [stkR_congr eC] at hbud
  have hscr := Scr.of_post (m0 := s.mem) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, hbig, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_, ?_, hx15, hdf, hra⟩
  · rw [← hPacc, ← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + (2 * xl + 3) / 4 * 4 ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hPacc, ← hacc2]; exact a3, a4⟩
  · intro hn
    by_cases hc : stLen s.mem st + (2 * xl + 3) / 4 * 4 ≤ stCap s.mem st
    · exact absurd (hsame hc) hn
    · exact hmem (by omega)

theorem mfTrans {m₀ m₁ m₂ : Memory} {rs rs' : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs)
    (h₂ : MemFrame m₁ m₂ rs') : MemFrame m₀ m₂ (rs ++ rs') where
  readLE a k ho := by
    rw [outside_append] at ho
    rw [h₂.readLE a k ho.2, h₁.readLE a k ho.1]
  accessible a k w := by rw [h₂.accessible, h₁.accessible]


/-- the continuation at the loop head (iteration `i`) -/
def HeadK (impl : List Amd64.Segment) (R : RtInv) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (Q : State → Prop) (i : Nat) : Prop :=
  ∀ S : State, S.rip = BitVec.ofNat 64 head → S.regs 4 = s.regs 4 - 192#64 → S.regs 5 = s.regs 4 - 8#64 →
    S.regs 14 = s.regs 14 → S.fsBase = s.fsBase → S.xmm 15 = 0#128 → S.df = false →
    S.regs 0 = BitVec.ofNat 64 i → S.regs 3 = BitVec.ofNat 64 (2 * xl.toNat) →
    S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat) → S.regs 7 = xl → S.regs 6 = xp → S.regs 8 = BitVec.ofNat 64 t →
    S.regs 9 = zl → S.regs 10 = zp →
    Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 i S.mem →
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) S Q

/-- the `CALL runtime.memclrNoHeapPointers` -/
abbrev callClr : Nat := segAddr Extracted.program fn + 0xe0

/-- the continuation at `CALL runtime.memclrNoHeapPointers` (proved by `BasicSqrClr.clr`; taken as a premise by the
prologue `pro2`/`pro3`, so that the prologue modules compile in parallel with the loop/epilogue chain — ROW-TIME LESSON) -/
def ClrK (impl : List Amd64.Segment) (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64)
    (s : State) : Prop :=
  ∀ (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat),
    Env R b H L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1 →
    ∀ (Q : State), Q.rip = BitVec.ofNat 64 callClr → Q.regs 4 = s.regs 4 - 192#64 →
    Q.regs 5 = s.regs 4 - 8#64 → Q.regs 14 = s.regs 14 → Q.fsBase = s.fsBase →
    Q.xmm 15 = 0#128 → Q.df = false →
    Q.regs 0 = BitVec.ofNat 64 t → Q.regs 3 = BitVec.ofNat 64 (16 * xl.toNat) →
    Mem R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1
      (stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4) Q.mem →
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) Q fun s' =>
      RegsOK s s' ∧ Post R b H L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s'

end FvModexp.Amd64.Q.BasicSqr
