import FvModexp.Proofs.Arm64.Top.RunD3J
import FvModexp.Proofs.Arm64.Top.RunD3ZDefs

/-! # `Run` (arm64): `Z2` to `J2` when the `copy` source equals the fresh buffer (`memmove` skipped) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d3zE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 L2 b2 S2 →
      (S2.regs 0).toNat = S2.mem.readLE (s.sp.toNat - 192) 8 → (S2.regs 1).toNat = S2.mem.readLE (s.sp.toNat - 184) 8 →
      S2.pc = BitVec.ofNat 64 pcD3 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q)
    (U : State) (Lk : List (Nat × Nat)) (bk B src : Nat) (hj : JoinZ3 R b L c p len cp s ret Lk bk B src 0 U)
    (hpc : U.pc = BitVec.ofNat 64 pcZ3) (heq : B = src) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  have henv0 := henv
  have hin0 := hin
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hz1, hz2, hz3,
    hl0, hl1, hl2, hnz, hlg, hr0, hy1, hy2, hsrc1, hsrc2, hB48, hBacc, hBH, hBW, hBrt, hBsep, hBv, hpst, -, hdS, hinS, hcS,
    hext, hbud, hinv, hLsS, hMF, hLF, hop0, hop1, hopA, -⟩ := hj
  subst heq
  simp only [stk] at hg3 hb' ha hw hout
  have hr0' : U.regs 0 = BitVec.ofNat 64 B := by
    apply BitVec.eq_of_toNat_eq; rw [hr0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs2, hs3, hs4, hs5, hs6, hy1, hy2, hr0', hIe, toInt_small] until [pcJ3]
  refine d3join impl hap R hmk hokS b L c p len cp ret hret s henv0 hin0 Q hbudD hk _ Lk bk B ?hj (by janus_simp)
  case hj =>
  refine ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hs1], by janus_simp [hs2], by janus_simp [hs3], by janus_simp [hs4],
     by janus_simp [hs5], by janus_simp [hs6], by janus_simp [hs7], by janus_simp [hs8], by janus_simp [hs9],
     by janus_simp [hz1], by janus_simp [hz2], by janus_simp [hz3], hl0, hl1, hl2, hnz,
     by janus_simp [hr0], by janus_simp [hs3], hB48,
     Memory.accessible_read_of_write _ hBacc, hBH, (by rcases hBW with h | h; exact Or.inl h; exact Or.inr (Or.inr h)),
     (fun j hj => (hBv j hj).trans (padByte_past (Nat.le_trans hpst (Nat.add_le_add_left (Nat.zero_le j) _))).symm), hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF, hop0, hop1, hopA⟩

end FvModexp.Arm64.Run
