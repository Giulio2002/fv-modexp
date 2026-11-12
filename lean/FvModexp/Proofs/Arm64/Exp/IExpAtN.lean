import FvModexp.Proofs.Arm64.Exp.IExpDefs

/-! # `(*Int).exp` (arm64): `AtN` at `nat.expNN`'s return (`atN_of`) and `z`'s header there (`AtN.hdr`) (pure) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntOK IntPre IntPost IntV arrW)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`AtN`** at `expNN`'s return, from `ExpSpec`'s precondition, the frame of segments A-C and `PostNil` -/
theorem atN_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above K : Nat}
    {costF : Nat → Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (hK : K + 1632 ≤ stk) (hab : 48 ≤ above)
    {zp zl zc yp yl mp n : Nat}
    (ez8 : s.mem.readLE (zA + 8) 8 = zp) (ez16 : s.mem.readLE (zA + 16) 8 = zl)
    (ez24 : s.mem.readLE (zA + 24) 8 = zc)
    (ey8 : s.mem.readLE (yA + 8) 8 = yp) (ey16 : s.mem.readLE (yA + 16) 8 = yl)
    (em8 : s.mem.readLE (mA + 8) 8 = mp) (em16 : s.mem.readLE (mA + 16) 8 = n)
    (hcost : 24 + ExpN.NCost costF costR costS costP zl yl n 0 (Nat.log2 (natVal s.mem mp n)) ≤ B)
    {S3 S4 : State} (hsp3 : S3.sp = BitVec.ofNat 64 (s.sp.toNat - 320)) (h28 : S3.regs 28 = s.regs 28)
    (hF3 : MemFrame s.mem S3.mem [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)])
    (hpost : ExpN.PostNil R b L K costF costR costS costP zp zc zp zl yp yl mp n S3 S4) :
    (∀ a k, ((s.sp.toNat - 328 ≤ a ∧ a + k ≤ s.sp.toNat - 312) ∨ (s.sp.toNat - 200 ≤ a ∧ a + k ≤ s.sp.toNat + 48)) →
      S4.mem.readLE a k = S3.mem.readLE a k) ∧
    ∃ p l c b' L', S4.regs 0 = BitVec.ofNat 64 p ∧ S4.regs 1 = BitVec.ofNat 64 l ∧ S4.regs 2 = BitVec.ofNat 64 c ∧
      AtN R b B L stk above s zA (IntV s.mem zA ^ IntV s.mem yA % IntV s.mem mA) p l c b' L' S4.mem := by
  obtain ⟨⟨-, ⟨-, hstk, -, -⟩, -, hrt, -, -, hLs, -⟩, -, -, -, -, hops, -⟩ := hpre
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  have hom := hops mA (by simp)
  clear hops
  obtain ⟨⟨-, -, -, -, -, hzL, hzlc, -, -⟩, -, hzO, -, -⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, -, hylc, -, -⟩, -, hyO, -, -⟩ := hoy
  obtain ⟨⟨-, -, -, -, -, -, hmlc, -, -⟩, -, hmO, -, -⟩ := hom
  obtain ⟨p, l, c, h0, h1, h2, hv, hnm, hlc, hc40, L', b', hx, hb, hinv, hnl, hd, hMF, hLF⟩ := hpost
  have hst : stk ≤ s.sp.toNat := hstk
  have hS3 : S3.sp.toNat = s.sp.toNat - 320 := by rw [hsp3, BitVec.toNat_ofNat]; omega
  have hF3w : MemFrame s.mem S3.mem [(s.sp.toNat - 328, s.sp.toNat + 48)] :=
    hF3.mono fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hvw : ∀ {a q k : Nat}, s.mem.readLE (a + 8) 8 = q → s.mem.readLE (a + 16) 8 = k →
      k ≤ s.mem.readLE (a + 24) 8 →
      (0 < s.mem.readLE (a + 24) 8 → Outside (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8)
        (win s stk above)) → natVal S3.mem q k = natVal s.mem q k := by
    intro a q k e8 e16 hlc' hO
    subst e8
    exact natVal_eq0 hlc' (fun h => by
      have := hO h; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega) hF3w
  have evz := hvw ez8 ez16 (ez16 ▸ hzlc) hzO
  have evy := hvw ey8 ey16 (ey16 ▸ hylc) hyO
  have evm := hvw em8 em16 (em16 ▸ hmlc) hmO
  rw [evz, evy, evm] at hv
  rw [evm] at hb
  have hpp : 0 < c → p % 2 ^ 64 = p := fun hc => Nat.mod_eq_of_lt (by have := (hnl hc).2.2.2; omega)
  have hpe : BitVec.ofNat 64 (p % 2 ^ 64) = BitVec.ofNat 64 p := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]
  have hz' : 0 < zc → zp + 8 * zc ≤ s.sp.toNat - stk ∨ s.sp.toNat + above ≤ zp := fun h => by
    have := hzO (ez24 ▸ h); rw [ez8, ez24] at this
    simp only [win, outside_cons, outside_nil, and_true] at this; exact this
  rw [winA, hS3] at hMF
  refine ⟨fun a k hak => Memory.readLE_congr fun i hi => ?_, p % 2 ^ 64, l, c, b', L', h0.trans hpe.symm, h1, h2,
    ⟨?_, ?_, hlc, hc40.1, Nat.mod_lt _ (by omega), hx,
    by omega, by rw [← h28]; exact hinv, ?_, ?_, ?_, ?_⟩⟩
  · -- the slots of `(*Int).exp`'s frame that `expNN` does not write
    exact MemFrame.byte hMF (out_slot hst hK hab hrt hz' hak hi)
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp only [RunIface.IntV]; rw [ez8, ez16, ey8, ey16, em8, em16]
      simp only [natVal_zero] at hv ⊢; exact hv
    · rw [hpp (by omega)]; simp only [RunIface.IntV]; rw [ez8, ez16, ey8, ey16, em8, em16]; exact hv
  · rcases Nat.eq_zero_or_pos l with hl | hl
    · exact Or.inl hl
    · rw [hpp (by omega)]; exact hnm
  · intro hc; rw [hpp hc]; exact hnl hc
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · exact Or.inl hc
    · rw [hpp hc, ez8, ez24]
      rcases hd with ⟨h, -⟩ | h | h
      · omega
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · -- memory frame, byte by byte
    refine MemFrame.of_bytes (fun a ho => ?_) (fun a k w => by rw [hMF.accessible, hF3.accessible])
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hoR, hoW⟩, hoA⟩ := ho
    have h3 := out_arrW hoA; rw [ez8, ez24] at h3
    obtain ⟨k1, k2⟩ := out_atN hst hK hab hoR hoW h3
    rw [MemFrame.byte hMF k1]; exact MemFrame.byte hF3 k2
  · refine LiveFrame.of_bytes fun a hin ho => ?_
    have h3 := out_arrW ho; rw [ez8, ez24] at h3
    rw [LiveFrame.byte hLF hin h3]
    obtain ⟨r, hr, e1, e2⟩ := hin
    exact MemFrame.byte hF3 (out_live hst hab (by omega) (hLs r hr) e1 e2)

end FvModexp.Arm64.IExp
