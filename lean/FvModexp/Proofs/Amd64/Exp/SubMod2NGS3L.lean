import FvModexp.Proofs.Amd64.Exp.SubMod2NGS3D

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: the `x' < y'` branch `z = z.sub(y', x')` → `J3G` (agent infra s48; the result in
`z`'s array or a fresh one)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at the `nat.sub` entry of the `x' < y'` branch (`z.sub(y', x')`, return address `+0x2ac`) -/
theorem s3Glt (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hsub : SubHypR0 impl R) {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {l1 p2 l2 c2 : Nat} {L2 : List (Nat × Nat)} {b2 : Nat}
    (S2 : State) (hpc : S2.rip = BitVec.ofNat 64 6183136) (hsp : (S2.regs 4).toNat = (s.regs 4).toNat - 136)
    (hrd : S2.mem.readLE (S2.regs 4).toNat 8 = 6216524) (h14 : S2.regs 14 = s.regs 14) (hfs : S2.fsBase = s.fsBase)
    (hx15 : S2.xmm 15 = 0) (hdf : S2.df = false)
    (h0 : S2.regs 0 = BitVec.ofNat 64 zp) (h3 : S2.regs 3 = BitVec.ofNat 64 zl) (h1 : S2.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S2.regs 7 = BitVec.ofNat 64 p2) (h6 : S2.regs 6 = BitVec.ofNat 64 l2) (h8 : S2.regs 8 = BitVec.ofNat 64 c2)
    (h9 : S2.regs 9 = BitVec.ofNat 64 zp) (h10 : S2.regs 10 = BitVec.ofNat 64 l1) (h11 : S2.regs 11 = BitVec.ofNat 64 zc)
    (hrt : Rt R b L s zp zc n 2 S2.mem L2 b2) (hfw : Fw s S2.mem zp zl zc yp n)
    (hv1 : natVal S2.mem zp l1 = natVal s.mem zp zl % 2 ^ n) (hn1 : NatNorm S2.mem zp l1) (hW1 : l1 ≤ W n)
    (hv2 : natVal S2.mem p2 l2 = natVal s.mem yp yl % 2 ^ n) (hn2 : NatNorm S2.mem p2 l2) (hW2 : l2 ≤ W n)
    (hlc2 : l2 ≤ c2) (hc2 : c2 < 2 ^ 40) (hlc1 : l1 ≤ zc) (hp2 : p2 < 2 ^ 64) (hy2 : Y2 R L2 S2.mem s zp zc p2 l2)
    (k3 : J3G impl R b L op zp zl zc yp yl yc n s)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n) :
    GoalG impl R b L zp zl zc yp yl n s S2 := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, hn1', -, hzl, ⟨hz64, -⟩, hzc, -, -,
    -, -, hzlive, hzw, -⟩ := id hpre
  have hent := hpre.ent
  have hx1 := x1_of hpre hrt hlc1
  simp only [W] at hW1 hW2
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hs4 : 4576 ≤ (s.regs 4).toNat := by omega
  have hll : l1 ≤ l2 := by
    rcases (SubMod2N.cmp_lt_iff S2.mem zp l1 p2 l2 hn1 hn2).2 (by rw [hv1, hv2]; exact hlt) with h | ⟨h, -⟩ <;> omega
  refine subCall0 hap hsub (zp := zp) (zl := zl) (zc := zc) (xp := p2) (xl := l2) (xc := c2) (yp := zp) (yl := l1)
    (yc := zc) (sp' := (s.regs 4).toNat - 136) (g := (s.regs 14).toNat) (ra := 6216524) (M := S2.mem)
    (bx39 := by omega)
    (ra_of hap (by decide) 0x2ac (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hpc hrd h0 h3 h1 h7 h6 h8 h9 h10 h11 hx15 hdf rfl hsp (by rw [h14])
    (subPre0_of hpre hrt (by omega) rfl hsp h14 hfs hll (by rw [hv1, hv2]; omega) hlc2 hlc1 hc2 hzc hW2 hp2 hz64
      (fun hz h => Or.inr ((hy2 h).2.2.2.2 hz)) (fun _ _ => Or.inl rfl)
      (fun h => by obtain ⟨a1, a2, a3, a4, -⟩ := hy2 h; exact ⟨a1, a2, a3, by omega⟩) hn2
      (fun h => by obtain ⟨a1, a2, a3, a4⟩ := hx1 h; exact ⟨a1, a2, a3, by omega⟩) hn1)
    fun s'' p' n' c' L3 b3 hpc'' hsp'' h14'' hx'' hfs'' hdf'' hrg'' e0 e1 e2 hv hnorm hlc hln hLE hb3 hinv3 hlive3
      hor3 hF3 hLF3 hreuse hc40 hp64' => ?_
  refine k3 s'' p' n' c' L3 b3 hpre hpc'' ?_ ⟨h14''.trans h14, hfs''.trans hfs, hx''.trans (hx15.trans hent.2.2.2.1.symm),
      hdf''.trans hdf⟩ e0 e1 e2 (fw_call hs4 hout hzw (Or.inl rfl) (by omega) (by omega) hfw hF3)
    (rt_call hrt hs4 (by omega) (by omega) (Or.inl rfl) hrg'' hF3 hLF3 hLE hb3 (makeCost_le_w (by simp only [W]; omega))
      hinv3 (fun hc => ?_)) hlive3
    (by rcases hor3 with h | ⟨h1, h2⟩; exact Or.inl h; exact Or.inr ⟨h1, fresh_of hrt.2.2.2.1 h2⟩)
    hc40 hp64' hlc (fun hW => hreuse (by simp only [W] at hW; omega)) hlt (by rw [hv, hv1, hv2]) hnorm
    (by simp only [W]; omega)
  · rw [hsp'']; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  · obtain ⟨c1, c2, c3, c4⟩ := hrt.2.2.2.2.2.2 hc
    exact ⟨c1, hLE.held c2, by rw [hF3.accessible]; exact c3, c4⟩

end FvModexp.Amd64.SubMod2N
