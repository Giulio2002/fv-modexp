import FvModexp.Proofs.Arm64.Exp.EvNP
import FvModexp.Proofs.Arm64.Exp.EvenNHyp

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the join points around the two `nat.expNN` calls (agent infra)

* `CapW R L m0 st p c`: the last capacity word of an operand (`x`, `y`) is held at the entry and apart from the entry
  free part of the stack — so `nat.expNN`'s alias test (`alias(z, x)`: same last capacity word) never fires for a
  located scratch `z` (`noAlias`), and an empty `nat.expNN` result is the scratch itself (`ExpNNHypNE0`).
* `J6` (`exp1R`): `m1`, `m2` in their slots, `z1 = x^y mod m1` with its array located (also when empty).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the last capacity word of an operand is held at the entry and apart from the entry free part -/
@[reducible] def CapW (R : RtInv) (L : List (Nat × Nat)) (m0 : Memory) (st p c : Nat) : Prop :=
  0 < c → Held R L (p + 8 * c - 8) 8 ∧ Apart (p + 8 * c - 8) 8 (free m0 st).1 (free m0 st).2

/-- a located array never has the same last word as a `CapW` operand -/
theorem noAlias {R : RtInv} {L : List (Nat × Nat)} {m0 : Memory} {st t k p c : Nat} (hl : Loc R L m0 st t k)
    (hk : 0 < k) (hc : CapW R L m0 st p c) : ¬ (0 < c ∧ t + 8 * k = p + 8 * c) := by
  rintro ⟨c0, e⟩
  obtain ⟨hh, hf⟩ := hc c0
  rcases hl with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · simp only [free, Apart] at hf; omega
  · have := hfresh hh hap hin; unfold Apart at this; omega

/-- the join point `exp1R` (return of `z1 = z1.expNN(stk, x, y, m1, false)`): `m1`, `m2` in their slots, slot 224 =
`2·max`, `z1 = (pz, lz, cz)` of value `x^y mod 2^n`; its array (the scratch when `cz = 0`) apart from `m1`, `m2` -/
structure J6 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ3 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 exp1R
  r0 : S.regs 0 = BitVec.ofNat 64 pz
  r1 : S.regs 1 = BitVec.ofNat 64 lz
  r2 : S.regs 2 = BitVec.ofNat 64 cz
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s224 : S.mem.readLE (sp + 224) 8 = 2 * max l1 l2
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  z1e : cz = 0 → LN R L s.mem st S.mem L1 pz 0 (2 * max l1 l2) 0
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  ze1 : cz = 0 → Apart pz (8 * (2 * max l1 l2)) p1 (8 * c1)
  ze2 : cz = 0 → Apart pz (8 * (2 * max l1 l2)) q (8 * a2 ml (nE s mp ml))

/-- `nat.expNN`'s program is inside `LibNE` -/
theorem libN_sub : ∀ x, ExpN.names.contains x = true → LibNE.names.contains x = true := by
  have h : LibN.names.Sublist LibNE.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem libN_nf : ExpN.names.contains fn = false := by decide +kernel

theorem expN_a : segAddr Extracted.program ExpN.fn = 1786544 := by decide

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- a `nat.expNN` result (empty, the destination `(r, k)` reused, or fresh) is a live local nat -/
theorem LN.of_expN (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {r k : Nat}
    (hd : DL R L s.mem st M L1 r k) {M' : Memory} {L2 : List (Nat × Nat)} {p l c v : Nat}
    (hv : natVal M' p l = v) (hn : NatNorm M' p l) (hlc : l ≤ c) (hc40 : c < 2 ^ 40) (hlv : NatLive M' R L2 p c)
    (hres : c = 0 ∨ (p = r ∧ c = k) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L1)) (hx : LiveExt R L1 L2)
    (hsb : StackBackL R L1 L2 st M M') (hrs : ResSep M M' st p c) : LN R L s.mem st M' L2 p l c v := by
  refine ⟨⟨hc40, hlv, fun hc => ?_⟩, hlc, hv, hn⟩
  rcases hres with h0 | ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · omega
  · obtain ⟨l1, o1⟩ := hd.2.2 hc
    exact ⟨l1, o1.back hx hsb.1⟩
  · exact ⟨Or.inr ⟨hin, fun r hr => hap r (h.le.mem_old hr)⟩,
      ob_fresh h.sok (WC.cap0 hP h) hin hap (hlv hc).2.1 hrs hc⟩

/-- an empty scratch destination as a live local nat of value `0` -/
theorem DL.ln0 {m0 M : Memory} {L1 : List (Nat × Nat)} {r k : Nat} (hd : DL R L m0 st M L1 r k) :
    LN R L m0 st M L1 r 0 k 0 :=
  ⟨hd, Nat.zero_le _, rfl, Or.inl rfl⟩

/-- a destination through a step keeping accessibility, with `StackBack` -/
theorem DL.step {m0 M M' : Memory} {L1 L2 : List (Nat × Nat)} {p c : Nat} (hd : DL R L m0 st M L1 p c)
    (hx : LiveExt R L1 L2) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hsb : StackBack R L1 L2 st M M') : DL R L m0 st M' L2 p c := by
  obtain ⟨c40, hlv, hlo⟩ := hd
  refine ⟨c40, fun hc => ?_, fun hc => ⟨(hlo hc).1, (hlo hc).2.back hx hsb⟩⟩
  obtain ⟨a1, a2, a3, a4⟩ := hlv hc
  exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩

end

/-- the level after `z2 = stk.nat(2·max(len m1, len m2))` -/
@[reducible] def ℓ4 (s : State) (st mp ml l1 l2 : Nat) : Nat := ℓ3 s st mp ml l1 l2 + StackNat.rnd (2 * max l1 l2)

/-- the join point `nat4R` (return of `z2 = stk.nat(2·max)`): `J6`'s locals, `z1` in the slots `264/152/160`, the
scratch `z2 = (t, 2·max, 2·max)` apart from `m1`, `m2` and `z1`'s array -/
structure J7 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz t : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 nat4R
  r0 : S.regs 0 = BitVec.ofNat 64 t
  r1 : S.regs 1 = BitVec.ofNat 64 (2 * max l1 l2)
  r2 : S.regs 2 = BitVec.ofNat 64 (2 * max l1 l2)
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s224 : S.mem.readLE (sp + 224) 8 = 2 * max l1 l2
  s264 : S.mem.readLE (sp + 264) 8 = pz
  s152 : S.mem.readLE (sp + 152) 8 = lz
  s160 : S.mem.readLE (sp + 160) 8 = cz
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  z1e : cz = 0 → LN R L s.mem st S.mem L1 pz 0 (2 * max l1 l2) 0
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  ze1 : cz = 0 → Apart pz (8 * (2 * max l1 l2)) p1 (8 * c1)
  ze2 : cz = 0 → Apart pz (8 * (2 * max l1 l2)) q (8 * a2 ml (nE s mp ml))
  d4 : DL R L s.mem st S.mem L1 t (2 * max l1 l2)
  tm1 : Apart t (8 * (2 * max l1 l2)) p1 (8 * c1)
  tm2 : Apart t (8 * (2 * max l1 l2)) q (8 * a2 ml (nE s mp ml))
  tz1 : 0 < cz → Apart t (8 * (2 * max l1 l2)) pz (8 * cz)
  tz1e : cz = 0 → Apart t (8 * (2 * max l1 l2)) pz (8 * (2 * max l1 l2))

end FvModexp.Arm64.ExpEven
