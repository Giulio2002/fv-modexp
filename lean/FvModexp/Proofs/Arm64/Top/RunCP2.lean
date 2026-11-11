import FvModexp.Proofs.Arm64.Top.RunCPDefs
import FvModexp.Proofs.Common.GenReg
import FvModexp.Proofs.Arm64.MemmoveZero

/-! # `Run` (arm64): `P` to the return — `copy(buf[modLen - len(v):], v)` (`memmove`, or skipped) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cp2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokM : ∀ d sr n, n ≤ 1024 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (W : Nat) (hW : 4800 ≤ W)
    (henv : CallEnv R L s W 40) (Q : Outcome → Prop)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b (okB s p len) L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (U : State) (Lk : List (Nat × Nat)) (bk vp vn buf : Nat) (hj : JoinP R b L p len s ret W Lk bk vp vn buf U)
    (hpc : U.pc = BitVec.ofNat 64 pcP) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hs3, hl2, hsv, hsn, hlt, hr0, hB48, hBacc, hBz, hBL, hBrt, hBsep, hvv, hvf,
    hdS, hext, hbud, hinv, hLsS, hMF, hLF⟩ := hj
  have hr0' : U.regs 0 = BitVec.ofNat 64 buf := by rw [← hr0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hI4 := toInt_small (BitVec.ofNat 64 vn) (by simp; omega)
  have hmask := padMask (hdrV s p len 2) vn hlt hl2
  have hlenv := padLen (hdrV s p len 2) vn hlt hl2
  obtain ⟨d, hdd⟩ : ∃ d, (if vn = 0 then 0 else hdrV s p len 2 - vn) = d := ⟨_, rfl⟩
  rw [hdd] at hmask
  have hd' : d = 0 ∧ vn = 0 ∨ d + vn = hdrV s p len 2 ∧ 0 < vn := by subst hdd; split <;> omega
  have hda : BitVec.ofNat 64 buf + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + buf) := bv_add_of_lt _ _ (by omega)
  janus_run [hm1, hm2, hs3, hsv, hsn, hr0', hI4, hmask, hlenv, hda] until [segAddr Extracted.program fn + 0x8dc,
    segAddr Extracted.program fn + 0x8f0]
  · -- `memmove` skipped: source = destination, only possible for `len(v) = 0`
    have hvp : vp < 2 ^ 64 := by rw [← hsv]; exact Memory.readLE_lt _ _ 8
    have hv0 : vn = 0 := by
      rcases Nat.eq_zero_or_pos vn with h | h
      · exact h
      · obtain ⟨-, -, hap', -⟩ := hvf h
        unfold Apart at hap'; rw [Nat.mod_eq_of_lt hvp] at hbr; omega
    subst hv0
    have hr0 : resV s p len = 0 := by rw [← hvv]; rfl
    janus_run [hm1, hm2, hs3, hsv, hsn, hr0', hI4, hmask, hlenv, hda]
    refine hOk _ ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29, hm2, regFP],
      by janus_simp [h18, regPlatform]⟩ ⟨by janus_simp, by janus_simp [hs3], ?v⟩
      ⟨Lk, bk, hext, hbud, ?inv, ?held, ?mf, ?lf⟩
    case v => janus_simp; rw [hr0]; exact beVal_zeros fun i hi => hBz i hi
    case inv => dsimp only; exact hinv
    case held => janus_simp; intro _; exact Or.inl hBL
    case mf => dsimp only; exact hMF
    case lf => dsimp only; exact hLF
  · -- `memmove(buf + d, v, len(v))`
    have hvp : vp < 2 ^ 64 := by rw [← hsv]; exact Memory.readLE_lt _ _ 8
    rw [Nat.mod_eq_of_lt hvp] at hbr
    have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
      MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
    have hmvok : R.ok (cA "runtime.memmove") [d + buf, vp, vn] := hokM _ _ _ (by omega)
    have hgS : U.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
      hMF.readLE _ _ (by
        simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
        unfold Apart at hga; exact ⟨hgr, by omega⟩)
    unfold Apart at hga
    have hbW : buf + hdrV s p len 2 ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ buf := by
      have := InRanges.apart hBrt hout; unfold Apart at this; omega
    have hLSc : ∀ r ∈ Lk, (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 624 - 4096 ∨ s.sp.toNat - 624 - 8 ≤ r.fst) ∧
        (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 624 + 8 ∨ s.sp.toNat - 624 + 8 + 24 ≤ r.fst) := by
      intro r hr; have := hLsS r hr
      simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this; omega
    have hwS : U.mem.accessible (s.sp.toNat - W) (W + 40) true = true := by rw [hMF.accessible]; exact hw
    rcases Nat.eq_zero_or_pos vn with hv0 | hv0
    · -- `memmove(buf, v, 0)` (`len(v) = 0`, `v`'s pointer arbitrary): the zero-length contract (Janus PR #2)
      subst hv0
      have hd0 : d = 0 := by omega
      subst hd0
      have hmz' : MemmoveZeroLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
        MemmoveZeroLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmz
      have hmvok : R.ok (cA "runtime.memmove") [0 + buf, vp, 0] := hokM _ _ _ (by omega)
      have hr0 : resV s p len = 0 := by rw [← hvv]; rfl
      set_option janus.callRegions true in
      janus_run [hm1, hm2, hs3, hsv, hsn, hr0', hI4, hmask, hlenv, hda, hgS] until
        [segAddr Extracted.program fn + 0x8e8] calls [hmz']
      rename_i m2 _ _ hLFm _ hMFm hinvm
      have hslot : m2.readLE (s.sp.toNat - 208) 8 = buf := by
        rw [hMFm.readLE _ _ (by
          simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
          exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩), Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      have hbuf : buf < 2 ^ 64 := by omega
      janus_run [hm1, hm2, hs3, hslot]
      refine hOk _ ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29, hm2, regFP],
        by janus_simp [h18, regPlatform]⟩ ⟨by janus_simp, by janus_simp [hs3], ?vv⟩
        ⟨Lk, bk, hext, hbud, ?inv, ?held, ?mf, ?lf⟩
      case vv =>
        janus_simp
        rw [hr0]
        refine beVal_zeros fun i hi => ?_
        have h1 := hLFm.readLE (buf + i) 1 (hBL.sub (by omega) (by omega)) (by simp only [Janus.outside_nil])
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at h1
        simp only [Memory.readLE_one] at h1
        rw [h1]; exact hBz i (by omega)
      case inv => dsimp only; exact hinvm
      case held => janus_simp; intro _; exact Or.inl hBL
      case mf =>
        dsimp only
        refine (hMF.trans ?w1 fun a n h => ⟨h, outW_w h⟩).trans hMFm fun a n h => ⟨h, ?w2⟩
        case w1 => simp only [win]; janus_frame
        case w2 => simpa only [List.append_nil] using outW_cs hW h
      case lf =>
        dsimp only
        refine hLF.trans ⟨fun a n hin _ => ?_⟩ (fun _ _ h => h)
        have hin' := hext.inRanges_old hin
        have hU := (LiveFrame.of_win (L := L) (ex := []) (m := U.mem) (m' := U.mem.writeLE (s.sp.toNat - 208) 8 buf)
          (by simp only [win]; janus_frame) (fun r hr => hLsS r (hext.mem_old hr))).readLE a n hin trivial
        rw [← hU]
        exact hLFm.readLE a n hin' (by simp only [Janus.outside_nil])
    obtain ⟨hv48, hvacc, hvap, hvw⟩ := hvf hv0
    unfold Apart at hvap
    have hd1 : d + vn = hdrV s p len 2 := by omega
    set_option janus.callRegions true in
    janus_run [hm1, hm2, hs3, hsv, hsn, hr0', hI4, hmask, hlenv, hda, hgS] until
      [segAddr Extracted.program fn + 0x8e8] calls [hmv']
    rename_i m2 _ _ hMFm hLFm hinvm hcp
    have hdRt : InRanges (d + buf) vn R.rt := hBrt.sub (by omega) (by omega)
    have hslot : m2.readLE (s.sp.toNat - 208) 8 = buf := by
      rw [hMFm.readLE _ _ (by
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
        have := InRanges.apart hdRt hout
        refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
        unfold Apart at this; omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    have hbuf : buf < 2 ^ 64 := by omega
    janus_run [hm1, hm2, hs3, hslot]
    refine hOk _ ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29, hm2, regFP],
      by janus_simp [h18, regPlatform]⟩ ⟨by janus_simp, by janus_simp [hs3], ?vv⟩
      ⟨Lk, bk, hext, hbud, ?inv, ?held, ?mf, ?lf⟩
    case vv =>
      janus_simp
      rw [← hd1, beVal_add, beVal_zeros (m := m2) (q := buf) (n := d) fun i hi => ?zz, Nat.zero_mul,
        Nat.zero_add, ← hvv]
      case zz =>
        have h1 := hLFm.readLE (buf + i) 1 (hBL.sub (by omega) (by omega)) (by
          simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega)
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at h1
        simp only [Memory.readLE_one] at h1
        rw [h1]; exact hBz i (by omega)
      rw [Nat.add_comm buf d]
      apply beVal_congr'
      intro i hi
      rw [hcp i hi]
      have h1 := Memory.readLE_writeLE_of_disjoint (m := U.mem) (a := s.sp.toNat - 208) (n := 8) (b := vp + i) (k := 1)
        buf (by omega)
      rw [Memory.readLE_one, Memory.readLE_one] at h1
      exact BitVec.eq_of_toNat_eq h1
    case inv => dsimp only; exact hinvm
    case held => janus_simp; intro _; exact Or.inl hBL
    case mf =>
      dsimp only
      refine (hMF.trans ?w1 fun a n h => ⟨h, outW_w h⟩).trans hMFm fun a n h => ⟨h, outW_csd hW hdRt h⟩
      case w1 => simp only [win]; janus_frame
    case lf =>
      dsimp only
      refine hLF.trans ⟨fun a n hin _ => ?_⟩ (fun _ _ h => h)
      have hin' := hext.inRanges_old hin
      have hU := (LiveFrame.of_win (L := L) (ex := []) (m := U.mem) (m' := U.mem.writeLE (s.sp.toNat - 208) 8 buf)
        (by simp only [win]; janus_frame) (fun r hr => hLsS r (hext.mem_old hr))).readLE a n hin trivial
      rw [← hU]
      refine hLFm.readLE a n hin' ?_
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := hBsep r hr
      simp only [Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; omega

end FvModexp.Arm64.Run
