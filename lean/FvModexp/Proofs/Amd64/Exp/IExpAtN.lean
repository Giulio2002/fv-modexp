import FvModexp.Proofs.Amd64.Exp.IExpDefs

/-! # `(*Int).exp` (amd64; agent expmc s77, twin of the arm64 IExpAtN): `AtN` at `nat.expNN`'s return (`atN_of`) (pure)

At `expNN`'s entry `S3` (`RSP = t - 0x138`, `t` = `(*Int).exp`'s entry `RSP`) the memory differs from the entry memory
only in segments A-C's frame `[t - 0x138, t) ∪ [t + 8, t + 0x30)`; `expNN`'s window is `[t - 0x5d0 - K, t - 0xc0)`,
so the slots `[t - 0xc0, t + 0x30)` of `(*Int).exp`'s frame survive the call.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.ByteFrame

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IExp

open FvModexp.Amd64.RunIface (IntOK IntPre IntV)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`AtN`** at `expNN`'s return, from `ExpSpec`'s precondition, the frame of segments A-C and `PostNil` -/
theorem atN_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above K costD : Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (hK : K + 0x5d0 ≤ stk) (hab : 0x30 ≤ above)
    {zp zl zc yp yl mp n : Nat}
    (ez8 : s.mem.readLE (zA + 8) 8 = zp) (ez16 : s.mem.readLE (zA + 16) 8 = zl)
    (ez24 : s.mem.readLE (zA + 24) 8 = zc)
    (ey8 : s.mem.readLE (yA + 8) 8 = yp) (ey16 : s.mem.readLE (yA + 16) 8 = yl)
    (em8 : s.mem.readLE (mA + 8) 8 = mp) (em16 : s.mem.readLE (mA + 16) 8 = n)
    (hcost : 24 + ExpN.NCost costD costR costS costP zl yl n 0 (Nat.log2 (natVal s.mem mp n)) ≤ B)
    {S3 S4 : State} (hsp3 : S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x138)) (h14 : S3.regs 14 = s.regs 14)
    (hF3 : MemFrame s.mem S3.mem [((s.regs 4).toNat - 0x138, (s.regs 4).toNat),
      ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x30)])
    (hpost : ExpN.PostNil R b L K costD costR costS costP zp zc zp zl yp yl mp n S3 S4) :
    (∀ a k, (s.regs 4).toNat - 0xc0 ≤ a → a + k ≤ (s.regs 4).toNat + 0x30 → S4.mem.readLE a k = S3.mem.readLE a k) ∧
    ∃ p l c b' L', S4.regs 0 = BitVec.ofNat 64 p ∧ S4.regs 3 = BitVec.ofNat 64 l ∧ S4.regs 1 = BitVec.ofNat 64 c ∧
      AtN R b B L stk above s zA (IntV s.mem zA ^ IntV s.mem yA % IntV s.mem mA) p l c b' L' S4.mem := by
  obtain ⟨⟨-, ⟨hstk, -, -⟩, -, -, hrt, -, -, hLs, -, -⟩, -, -, -, -, hops, -⟩ := hpre
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  have hom := hops mA (by simp)
  clear hops
  obtain ⟨⟨-, -, -, -, -, -, hzlc, -, -, -⟩, -, hzO, -, -, -, -⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, -, hylc, -, -, -⟩, -, hyO, -, -, -, -⟩ := hoy
  obtain ⟨⟨-, -, -, -, -, -, hmlc, -, -, -⟩, -, hmO, -, -, -, -⟩ := hom
  obtain ⟨-, -, p, l, c, h0, h1, h2, hv, hnm, hlc, ⟨hc40, hp64⟩, L', b', hx, hb, hinv, hnl, hd, hMF, hLF⟩ := hpost
  generalize ht : (s.regs 4).toNat = t at *
  have hst : stk ≤ t := hstk
  have hS3 : (S3.regs 4).toNat = t - 0x138 := by rw [hsp3, BitVec.toNat_ofNat]; omega
  have hF3w : MemFrame s.mem S3.mem [(t - 0x138, t + 0x30)] :=
    hF3.mono fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hvw : ∀ {a q k : Nat}, s.mem.readLE (a + 8) 8 = q → s.mem.readLE (a + 16) 8 = k →
      k ≤ s.mem.readLE (a + 24) 8 →
      (0 < s.mem.readLE (a + 24) 8 → Outside (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8)
        (win s stk above)) → natVal S3.mem q k = natVal s.mem q k := by
    intro a q k e8 e16 hlc' hO
    subst e8
    exact natVal_eq0 hlc' (fun h => by
      have := hO h; simp only [win, ht, outside_cons, outside_nil, and_true] at this ⊢; omega) hF3w
  have evz := hvw ez8 ez16 (ez16 ▸ hzlc) hzO
  have evy := hvw ey8 ey16 (ey16 ▸ hylc) hyO
  have evm := hvw em8 em16 (em16 ▸ hmlc) hmO
  rw [evz, evy, evm] at hv
  rw [evm] at hb
  simp only [win, hS3] at hMF
  refine ⟨fun a k e1 e2 => Janus.Arm64.Memory.readLE_congr fun i hi => MemFrame.byte hMF ?_, p, l, c, b', L', h0, h1, h2,
    ⟨?_, hnm, hlc, hc40, hp64, hx, by omega, by rw [← h14]; exact hinv, hnl, ?_, ?_, ?_⟩⟩
  · -- the slots of `(*Int).exp`'s frame that `expNN` does not write
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hrt.of_sub (by omega) (by omega), by omega⟩, ?_⟩
    rcases Nat.eq_zero_or_pos zc with hz0 | hz0
    · subst hz0; omega
    · have := hzO (ez24 ▸ hz0); rw [ez8, ez24] at this
      simp only [win, ht, outside_cons, outside_nil, and_true] at this; omega
  · simp only [RunIface.IntV]; rw [ez8, ez16, ey8, ey16, em8, em16]; exact hv
  · rw [ez8, ez24]
    rcases hd with ⟨h, -⟩ | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · -- memory frame, byte by byte
    refine MemFrame.of_bytes (fun a ho => ?_) (fun a k w => by rw [hMF.accessible, hF3.accessible])
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hoR, hoW⟩, hoA⟩ := ho
    have h3 := out_arrW hoA; rw [ez8, ez24] at h3
    simp only [win, ht, outside_cons, outside_nil, and_true] at hoW h3
    rw [MemFrame.byte hMF (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨hoR, by omega⟩, h3⟩)]
    exact MemFrame.byte hF3 (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine LiveFrame.of_bytes fun a hin ho => ?_
    have h3 := out_arrW ho; rw [ez8, ez24] at h3
    rw [LiveFrame.byte hLF hin h3]
    obtain ⟨r, hr, e1, e2⟩ := hin
    have := hLs r hr
    simp only [win, ht, outside_cons, outside_nil, and_true] at this
    exact MemFrame.byte hF3 (by simp only [outside_cons, outside_nil, and_true]; omega)

end FvModexp.Amd64.IExp
