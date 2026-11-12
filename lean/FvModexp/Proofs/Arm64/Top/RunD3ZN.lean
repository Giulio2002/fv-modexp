import FvModexp.Proofs.Arm64.Top.RunD3J
import FvModexp.Proofs.Arm64.Top.RunD3ZDefs
import FvModexp.Proofs.Arm64.Top.RunDSlot

/-! # `Run` (arm64): `Z2` to `J2` when the `copy` source differs from the fresh buffer: `memmove` of 0 bytes -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d3zN (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 L2 b2 S2 →
      (S2.regs 0).toNat = S2.mem.readLE (s.sp.toNat - 192) 8 → (S2.regs 1).toNat = S2.mem.readLE (s.sp.toNat - 184) 8 →
      S2.pc = BitVec.ofNat 64 pcD3 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q)
    (U : State) (Lk : List (Nat × Nat)) (bk B src : Nat) (hj : JoinZ3 R b L c p len cp s ret Lk bk B src 0 U)
    (hpc : U.pc = BitVec.ofNat 64 pcZ3) (hne : B ≠ src) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  have henv0 := henv
  have hin0 := hin
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hz1, hz2, hz3,
    hl0, hl1, hl2, hnz, hlg, hr0, hy1, hy2, hsrc1, hsrc2, hB48, hBacc, hBH, hBW, hBrt, hBsep, hBv, hpst, -, hdS, hinS, hcS,
    hext, hbud, hinv, hLsS, hMF, hLF, hop0, hop1, hopA, -⟩ := hj
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
  unfold Apart at hga
  have hgS : U.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hgr, by omega, by omega⟩)
  have hwS : U.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : U.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hLS1 : ∀ r ∈ Lk, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hr0' : U.regs 0 = BitVec.ofNat 64 B := by
    apply BitVec.eq_of_toNat_eq; rw [hr0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hmvok : R.ok (cA "runtime.memmove") [B, src, 0] := hokM _ _ _ (by omega)
  have hsA : s.mem.accessible src 0 false = true := Memory.accessible_mono _ hpacc (by omega) (by omega)
  have hBA : s.mem.accessible B 0 true = true := Memory.accessible_mono _ hBacc (Nat.le_refl _) (by omega)
  have hBH0 : InRanges B 0 Lk ∨ Outside B 0 R.rt := hBH.sub (Nat.le_refl _) (by omega)
  have hn1 : (src = B) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hn2 : (B = src) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hn3 : (BitVec.ofNat 64 src = BitVec.ofNat 64 B) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
  have hn4 : (BitVec.ofNat 64 B = BitVec.ofNat 64 src) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
  have hgt : (0 < ((hdrV s p len 2 : Nat) : Int)) = True := by simp only [eq_iff_iff, iff_true]; omega
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs2, hs3, hs4, hs5, hs6, hy1, hy2, hr0', hIe, toInt_small, hn1, hn2, hn3, hn4, hgt]
    until [segAddr Extracted.program fn + 0x728] calls [hmv']
  rename_i m2 _ _ hMFm hLFm hinvm hcp
  have hm : ∀ a n w, U.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    simp only [hMF.accessible]
  have hdk' : Extracted.program.DataLoaded (U.mem.writeLE (BitVec.toNat s.sp - 264) 8 B) :=
    hdS.writeLE (by rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega))
  have hMFm' := hMFm
  rw [List.append_assoc] at hMFm'
  have hd2 : Extracted.program.DataLoaded m2 := by
    refine dataLoaded_frame hdk' (by rw [hrg1]; simp) hro hMFm' fun r hr _ => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Memory.accessible_writeLE]
    rcases hr with (rfl | rfl) | rfl
    · rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hm]; exact Memory.accessible_mono _ hBacc (Nat.le_refl _) (by dsimp only; omega)
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs2, hs3, hs4, hs5, hs6] until [pcJ3]
  have hB0 : InRanges B 0 R.rt := hBrt.sub (Nat.le_refl _) (by omega)
  have hMF2 : MemFrame s.mem m2 (R.rt ++ winA s stk 40) := by
    simp only [winA, stk] at hMF ⊢
    refine (hMF.trans ?w2 fun a n h => ⟨h, out_wA h⟩).trans hMFm fun a n h => ⟨h, ?o⟩
    case w2 => janus_frame
    case o => have := out_csd (k := 0) hb' hB0 h; simpa using this
  have hLsLk : LiveSep Lk (win s 4800 40) := hLs0
  have hLFS : LiveFrame U.mem m2 Lk [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsLk).trans
      (LiveFrame.drop (L := Lk) ⟨fun a n h hw => hLFm.readLE a n h hw⟩ (by simpa using hBsep)) (fun _ _ h => h)
  have hLF2 : LiveFrame s.mem m2 L [] := hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
  have hLx := LiveFrame.of_nil' hLF2 (winA s stk 40)
  have hpo' : Outside p.toNat len.toNat (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hco' : Outside c.toNat 3 (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hIn : InRanges B (hdrV s p len 2) Lk := by
    rcases hBH with h | h
    · exact h
    · have := InRanges.apart hBrt h; unfold Apart at this; omega
  refine d3join impl hap R hmk hokS b L c p len cp ret hret s henv0 hin0 Q hbudD hk _ Lk bk B ?hj (by janus_simp)
  case hj =>
  refine ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hs1], by janus_simp [hs2], by janus_simp [hs3], by janus_simp [hs4],
     by janus_simp [hs5], by janus_simp [hs6], by janus_simp [hs7], by janus_simp [hs8], by janus_simp [hs9],
     by janus_simp [hz1], by janus_simp [hz2], by janus_simp [hz3], hl0, hl1, hl2, hnz,
     by janus_simp, by janus_simp [hs3], hB48,
     Memory.accessible_read_of_write _ hBacc, hBH, (by rcases hBW with h | h; exact Or.inl h; exact Or.inr (Or.inr h)),
     ?bytes, hd2, fun a n h1 h2 => (hheld.sub h1 h2).readLE hMF2 hLx (hpo'.of_sub h1 (by omega)),
     hcheld.readLE hMF2 hLx hco', hext, hbud, hinvm, hLsS, hMF2, hLF2,
     OpDone.transportS hop0 (k := 2) (by omega) (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp) hLFS (fun _ _ h => h),
     OpDone.transportS hop1 (k := 2) (by omega) (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp) hLFS (fun _ _ h => h), OpsApart.transportS hopA (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp)⟩
  case bytes =>
    intro j hj
    dsimp only
    rw [← Memory.readLE_one, hLFS.readLE _ _ (hIn.sub (by omega) (by omega)) trivial, Memory.readLE_one]
    rw [hBv j hj, padByte_past (Nat.le_trans hpst (Nat.add_le_add_left (Nat.zero_le j) _))]

end FvModexp.Arm64.Run
