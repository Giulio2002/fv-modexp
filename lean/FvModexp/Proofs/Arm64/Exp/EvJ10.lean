import FvModexp.Proofs.Arm64.Exp.EvLZ
import FvModexp.Proofs.Arm64.Exp.SubMod2NG

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): empty-nat locations and the join `smR` (after `z1 = z1.subMod2N(z1, z2, n)`) (agent infra)

* `EL` (EvJ2): an empty local's pointer is `0` or a runtime pointer apart from the entry live set. `EL.sub` / `EL.subL` /
  `EL.win` / `EL.apart`: the obligations `stepC0` and `subMod2N`'s `PreG` ask of an EMPTY destination `(p, p)`.
* `J10` (`smR`, `X0..X2` = the result `(p3, l3, c3)` of `subMod2N`, value `Exp.subMod2N Z1 Z2 n`): `m1`, `m2`, `z2`, `z`
  kept, the result located (`z1`'s array or fresh) and apart from `m1`, `m2`, `z2`, `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

section
variable {R : RtInv} {L : List (Nat × Nat)} {p : Nat}

theorem EL.sub (h : EL R L p 0) {zs : List (Nat × Nat)} :
    ∀ a k, Outside a k R.rt → Outside a k zs → Outside a k [(p, p + 8 * 0)] := by
  intro a k ho _
  simp only [Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
  rcases h rfl with rfl | ⟨⟨r, hr, h1, h2⟩, -⟩
  · omega
  · have := MemFrame.outside_mem ho hr; omega

theorem EL.subL (h : EL R L p 0) {zs : List (Nat × Nat)} :
    ∀ a k, InRanges a k L → Outside a k zs → Outside a k [(p, p + 8 * 0)] := by
  intro a k ⟨r, hr, h1, h2⟩ _
  simp only [Nat.mul_zero, Nat.add_zero, outside_cons, outside_nil, and_true]
  rcases h rfl with rfl | ⟨-, hap⟩
  · omega
  · have := hap r hr; unfold Apart at this; omega

/-- an empty local is not strictly inside a range held at the entry -/
theorem EL.apart (h : EL R L p 0) {a n : Nat} (hh : Held R L a n) : Apart p (8 * 0) a n := by
  rcases h rfl with rfl | ⟨hin, hap⟩
  · unfold Apart; omega
  · exact hfresh hh (by simpa using hap) (by simpa using hin)

/-- … nor inside a range outside the runtime ranges -/
theorem EL.out (h : EL R L p 0) {a n : Nat} (ho : Outside a n R.rt) : Apart p (8 * 0) a n := by
  rcases h rfl with rfl | ⟨hin, -⟩
  · unfold Apart; omega
  · exact ((show InRanges p (8 * 0) R.rt by simpa using hin).apart ho).symm

/-- a result in the destination's array or fresh: empty-location from the destination's -/
theorem EL.of_res {L1 : List (Nat × Nat)} {pd cd c' : Nat} (hd : EL R L pd cd) (hx : LiveExt R L L1)
    (hor : (p = pd ∧ c' = cd) ∨ (InRanges p (8 * c') R.rt ∧ ApartAll p (8 * c') L1)) : EL R L p c' := by
  intro hc
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · exact hd hc
  · subst hc
    exact Or.inr ⟨by simpa using hin, fun r hr => by simpa using hap r (hx.mem_old hr)⟩

theorem EL.mono {L' : List (Nat × Nat)} (h : EL R L p 0) (hx : ∀ r ∈ L', r ∈ L) : EL R L' p 0 := fun e =>
  (h e).imp id fun ⟨hin, hap⟩ => ⟨hin, fun r hr => hap r (hx r hr)⟩

end

/-- `LibW` (the window / subMod2N / modInv program) is inside `LibNE` -/
theorem libW_sub : ∀ x, LibW.names.contains x = true → LibNE.names.contains x = true := by
  have h : LibW.names.Sublist LibNE.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem libW_nf : LibW.names.contains fn = false := by decide +kernel

/-- the join point `smR` (return of `z1 = z1.subMod2N(z1, z2, n)`): `X0..X2` = the result `(p3, l3, c3)` -/
structure J10 (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pw lw cw pZ cZ p3 l3 c3 : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 smR
  r0 : S.regs 0 = BitVec.ofNat 64 p3
  r1 : S.regs 1 = BitVec.ofNat 64 l3
  r2 : S.regs 2 = BitVec.ofNat 64 c3
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s256 : S.mem.readLE (sp + 256) 8 = pw
  s136 : S.mem.readLE (sp + 136) 8 = lw
  s144 : S.mem.readLE (sp + 144) 8 = cw
  s272 : S.mem.readLE (sp + 272) 8 = pZ
  s168 : S.mem.readLE (sp + 168) 8 = lw
  s176 : S.mem.readLE (sp + 176) 8 = cZ
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z2 : LN R L s.mem st S.mem L1 pw lw cw
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pw64 : pw < 2 ^ 64
  z2e : EL R L pw cw
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  zs : LZ R L st zp zc S.mem L1 pZ lw cZ
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  Za1 : 0 < cZ → Apart pZ (8 * cZ) p1 (8 * c1)
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)
  z3 : LN R L s.mem st S.mem L1 p3 l3 c3
    (Exp.subMod2N (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
      (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml)) (nE s mp ml))
  p364 : p3 < 2 ^ 64
  z3e : EL R L p3 c3
  ta1 : 0 < c3 → Apart p3 (8 * c3) p1 (8 * c1)
  ta2 : 0 < c3 → Apart p3 (8 * c3) q (8 * a2 ml (nE s mp ml))
  tw : 0 < c3 → 0 < cw → Apart p3 (8 * c3) pw (8 * cw)
  tZ : 0 < c3 → 0 < cZ → Apart p3 (8 * c3) pZ (8 * cZ)

end FvModexp.Arm64.ExpEven
