import FvModexp.Proofs.Amd64.Top.RunCPDefs

/-! # `Run` (amd64): `P` to the return — `copy(buf[modLen - len(v):], v)` (`memmove`, or skipped)

From `P` (`fn + 0xbf5`): `CX = modLen`, `DX = len(v)`, `SI = buf + ((modLen - len v) masked)`, `DI = len(v)`,
`BX = v`; `CMPQ BX, SI; JE` skips the copy; else `buf` is spilled at `0x190(SP)` (`e - 208`) and
`memmove(SI, BX, DI)` (call `fn + 0xc41`, return `fn + 0xc46`); return `(buf, modLen, modLen)`, `DI = SI = 0`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- The two stack-slot stores of `P` (`0x190(SP)` spill, return-address push at `-616`) stay inside the window
`[sp - W, sp + ab)`: the named closer of the `MemFrame` goals (was `janus_frame`, 46 s over four calls). -/
theorem frame_two_slots (m : Janus.Arm64.Memory) {sp W k1 k2 : Nat} (v1 v2 ab : Nat) (h1 : 8 ≤ k1) (h1' : k1 ≤ W)
    (h2 : 8 ≤ k2) (h2' : k2 ≤ W) (hW : W ≤ sp) :
    MemFrame m ((m.writeLE (sp - k1) 8 v1).writeLE (sp - k2) 8 v2) [(sp - W, sp + ab)] :=
  ((MemFrame.refl m _).writeLE v1 (List.mem_singleton_self _) (by omega) (by omega)).writeLE v2
    (List.mem_singleton_self _) (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cp2 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokM : ∀ d sr n, n ≤ 1024 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (W : Nat) (hW : 4800 ≤ W)
    (henv : CallEnv R L s W 40) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (Q : Janus.Amd64.Outcome → Prop)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b (okB s p len) L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (U : State) (Lk : List (Nat × Nat)) (bk vp vn buf : Nat) (hj : JoinP R b L p len s ret W Lk bk vp vn buf U)
    (hpc : U.rip = BitVec.ofNat 64 pcP) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hs3, hl2, hsv, hsn, hlt, hr0, hB48, hBacc, hBz, hBL, hBrt, hBsep, hvv,
    hvf, hdS, hext, hbud, hinv, hLsS, hMF, hLF⟩ := hj
  rw [hx0] at hx15
  rw [hdf0] at hdf
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hr0' : U.regs 0 = BitVec.ofNat 64 buf := by rw [← hr0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn5 : (BitVec.ofNat 64 (hdrV s p len 2)).toNat = hdrV s p len 2 := by simp; omega
  have hn1 : (BitVec.ofNat 64 vn).toNat = vn := by simp; omega
  have hs3' : U.mem.readLE ((s.regs 4).toNat - 472) 8 = (BitVec.ofNat 64 (hdrV s p len 2)).toNat := by rw [hs3, hn5]
  have hsn' : U.mem.readLE ((s.regs 4).toNat - 560) 8 = (BitVec.ofNat 64 vn).toNat := by rw [hsn, hn1]
  have hI4 := toInt_small (BitVec.ofNat 64 vn) (by simp; omega)
  have hmask := padMask64' (hdrV s p len 2) vn hlt hl2
  have hlenv := padLen64 (hdrV s p len 2) vn hlt hl2
  obtain ⟨d, hdd⟩ : ∃ d, (if vn = 0 then 0 else hdrV s p len 2 - vn) = d := ⟨_, rfl⟩
  rw [hdd] at hmask
  have hd' : d = 0 ∧ vn = 0 ∨ d + vn = hdrV s p len 2 ∧ 0 < vn := by subst hdd; split <;> omega
  have hda : BitVec.ofNat 64 buf + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + buf) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hvp : vp < 2 ^ 64 := by rw [← hsv]; exact Janus.Arm64.Memory.readLE_lt _ _ 8
  have hsv' : U.mem.readLE ((s.regs 4).toNat - 240) 8 = (BitVec.ofNat 64 vp).toNat := by
    rw [hsv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvp]
  janus64_run [hsp, hm1, hm2, hs3', hsn', hsv', hr0', hI4, hmask, hlenv, hda, BitVec.msb_eq_decide] until
    [segAddr Extracted.program fn + 0xc56, segAddr Extracted.program fn + 0xc33]
  · -- `memmove` skipped: source = destination, only possible for `len(v) = 0`
    have hv0 : vn = 0 := by
      rcases Nat.eq_zero_or_pos vn with h | h
      · exact h
      · obtain ⟨-, -, hap', -⟩ := hvf h
        unfold Apart at hap'; omega
    subst hv0
    have hd0 : d = 0 := by omega
    subst hd0
    have hr0 : resV s p len = 0 := by rw [← hvv]; rfl
    janus64_run [hsp, hm1, hm2, hs3', hsn', hsv', hr0', hn5, BitVec.msb_eq_decide]
    refine hOk _ ⟨by janus64_simp [hsp], by janus64_simp [hm2, regFP], by janus64_simp [h14, regG],
      by janus64_simp [hx15]⟩ ⟨by janus64_simp, by janus64_simp, ?v⟩
      ⟨by janus64_simp [hfs], by janus64_simp [hdf], Lk, bk, hext, hbud, ?inv, ?held, ?mf, ?lf⟩
    case v => janus64_simp; rw [hr0]; exact beVal_zeros fun i hi => hBz i hi
    case inv => dsimp only; exact hinv
    case held => janus64_simp; intro _; exact Or.inl hBL
    case mf => dsimp only; exact hMF
    case lf => dsimp only; exact hLF
  · -- `memmove(buf + d, v, len(v))`
    have hmv' : MemmoveLive64 (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
      MemmoveLive64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmv
    have hgS : U.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
      hMF.readLE _ _ (by
        simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
        unfold Apart at hga; exact ⟨hgr, by omega⟩)
    have hgA : U.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hMF.accessible]; exact hg2
    unfold Apart at hga
    have he : 4800 ≤ (s.regs 4).toNat := Nat.le_trans hW hb'
    obtain ⟨hcf1, hcf2, hcf3, hcf4⟩ := frame_call_factsW hW hal hg3 hga
    have hbW : buf + hdrV s p len 2 ≤ (s.regs 4).toNat - 4800 ∨ (s.regs 4).toNat + 40 ≤ buf := by
      have := InRanges.apart hBrt hout; unfold Apart at this; exact win_mono_out hW this
    have hLSm : ∀ r ∈ Lk, Outside r.fst (r.snd - r.fst)
        ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
            ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
          [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
      intro r hr; have := hLsS r hr
      simp only [win, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
      omega
    have hwS : U.mem.accessible ((s.regs 4).toNat - W) (W + 40) true = true := by rw [hMF.accessible]; exact hw
    rcases Nat.eq_zero_or_pos vn with hv0 | hv0
    · -- `memmove(buf, v, 0)` (`len(v) = 0`, `v`'s pointer arbitrary): the zero-length contract (Janus PR #2)
      subst hv0
      have hd0 : d = 0 := by omega
      subst hd0
      have hmz' : MemmoveZeroLive64 (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
        MemmoveZeroLive64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmz
      have hmvok : R.ok (cA "runtime.memmove") [0 + buf, vp, 0] := hokM _ _ _ (by omega)
      have hmvok' : R.ok (cA "runtime.memmove") [buf, vp, 0] := hokM _ _ _ (by omega)
      have hr0 : resV s p len = 0 := by rw [← hvv]; rfl
      set_option janus.callRegions true in
      janus64_run [hsp, hm1, hm2, hs3', hsn', hsv', hr0', hI4, hmask, hlenv, hda, hgS, BitVec.msb_eq_decide] until
        [segAddr Extracted.program fn + 0xc46] calls [hmz']
      rename_i _ _ _ _ m2 _ _ hLFm _ hMFm hinvm
      obtain ⟨hso1, hso2⟩ := slot_out_call (k := 208) hW hb' (by decide) (by decide) hout
      obtain ⟨hto1, hto2⟩ := slot_out_call (k := 472) hW hb' (by decide) (by decide) hout
      have hslot : m2.readLE ((s.regs 4).toNat - 208) 8 = buf := by
        rw [hMFm.readLE _ _ hso1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hso2,
          Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      have hs3m : m2.readLE ((s.regs 4).toNat - 472) 8 = (BitVec.ofNat 64 (hdrV s p len 2)).toNat := by
        rw [hMFm.readLE _ _ hto1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hto2,
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hs3']
      have hbuf : buf < 2 ^ 64 := by omega
      janus64_run [hsp, hm1, hm2, hs3m, hslot, hn5, BitVec.msb_eq_decide]
      refine hOk _ ⟨by janus64_simp [hsp], by janus64_simp [hm2, regFP], by janus64_simp [h14, regG],
        by janus64_simp [hx15]⟩ ⟨by janus64_simp, by janus64_simp, ?vv⟩
        ⟨by janus64_simp [hfs], by janus64_simp [hdf], Lk, bk, hext, hbud, ?inv, ?held, ?mf, ?lf⟩
      case vv =>
        janus64_simp
        rw [hr0]
        refine beVal_zeros fun i hi => ?_
        have hb1 := fresh_byte_out (w := 616) he (by decide) (by decide) hbW hi
        have hb2 := fresh_byte_out (w := 208) he (by decide) (by decide) hbW hi
        have h1 := hLFm.readLE (buf + i) 1 (hBL.sub (by omega) (by omega)) (by simp only [Janus.outside_nil])
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hb1,
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hb2] at h1
        simp only [Janus.Arm64.Memory.readLE_one] at h1
        rw [h1]; exact hBz i (by omega)
      case inv => dsimp only; exact hinvm
      case held => janus64_simp; intro _; exact Or.inl hBL
      case mf =>
        dsimp only
        refine (hMF.trans ?w1 fun a n h => ⟨h, outW_w h⟩).trans hMFm fun a n h => ⟨h, outW_cs2 hW h⟩
        case w1 => exact frame_two_slots _ _ _ _ (by decide) (Nat.le_trans (by decide) hW) (by decide) (Nat.le_trans (by decide) hW) hb'
      case lf =>
        dsimp only
        refine hLF.trans ⟨fun a n hin _ => ?_⟩ (fun _ _ h => h)
        have hin' := hext.inRanges_old hin
        have hU := (LiveFrame.of_win (L := L) (ex := []) (m := U.mem)
          (m' := (U.mem.writeLE ((s.regs 4).toNat - 208) 8 buf).writeLE ((s.regs 4).toNat - 616) 8 6639494)
          (frame_two_slots _ _ _ _ (by decide) (Nat.le_trans (by decide) hW) (by decide) (Nat.le_trans (by decide) hW) hb') (fun r hr => hLsS r (hext.mem_old hr))).readLE a n hin trivial
        rw [← hU]
        exact hLFm.readLE a n hin' (by simp only [Janus.outside_nil])
    · obtain ⟨hv48, hvacc, hvap, hvw⟩ := hvf hv0
      unfold Apart at hvap
      have hd1 : d + vn = hdrV s p len 2 := by omega
      have hmvok : R.ok (cA "runtime.memmove") [d + buf, vp, vn] := hokM _ _ _ (by omega)
      have hvw' := win_mono_out hW (by omega : (s.regs 4).toNat - W + (W + 40) ≤ vp ∨ vp + vn ≤ (s.regs 4).toNat - W)
      obtain ⟨hsf1, hsf2, hsf3, hsf4⟩ := fresh_call_facts (dst := vp) (n := vn) he (by omega)
      have hdW : d + buf + vn ≤ (s.regs 4).toNat - 4800 ∨ (s.regs 4).toNat + 40 ≤ d + buf := by omega
      obtain ⟨hdf1, hdf2, hdf3, hdf4⟩ := fresh_call_facts (dst := d + buf) (n := vn) he hdW
      have hdL : InRanges (d + buf) vn Lk := hBL.sub (by omega) (by omega)
      have hvaccU : U.mem.accessible vp vn false = true := by rw [hMF.accessible]; exact hvacc
      have hdaccU : U.mem.accessible (d + buf) vn true = true := by
        rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hBacc (by omega) (by omega)
      set_option janus.callRegions true in
      janus64_run [hsp, hm1, hm2, hs3', hsn', hsv', hr0', hI4, hmask, hlenv, hda, hgS, BitVec.msb_eq_decide] until
        [segAddr Extracted.program fn + 0xc46] calls [hmv']
      rename_i _ _ _ _ m2 _ _ hMFm hLFm hinvm hcp
      have hdRt : InRanges (d + buf) vn R.rt := hBrt.sub (by omega) (by omega)
      obtain ⟨hso1, hso2⟩ := slot_out_call (k := 208) hW hb' (by decide) (by decide) hout
      obtain ⟨hto1, hto2⟩ := slot_out_call (k := 472) hW hb' (by decide) (by decide) hout
      have hsoD : Outside ((s.regs 4).toNat - 208) 8 (R.rt ++
          [((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
            ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++ [(d + buf, d + buf + vn)]) := by
        have := fresh_slot (w := 208) (x := hdrV s p len 2) (n := hdrV s p len 2) he (by decide) (by decide) hbW (Nat.le_refl _)
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at hso1 ⊢
        exact ⟨hso1, by omega⟩
      have htoD : Outside ((s.regs 4).toNat - 472) 8 (R.rt ++
          [((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
            ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++ [(d + buf, d + buf + vn)]) := by
        have := fresh_slot (w := 472) (x := hdrV s p len 2) (n := hdrV s p len 2) he (by decide) (by decide) hbW (Nat.le_refl _)
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at hto1 ⊢
        exact ⟨hto1, by omega⟩
      have hslot : m2.readLE ((s.regs 4).toNat - 208) 8 = buf := by
        rw [hMFm.readLE _ _ hsoD, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hso2,
          Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      have hs3m : m2.readLE ((s.regs 4).toNat - 472) 8 = (BitVec.ofNat 64 (hdrV s p len 2)).toNat := by
        rw [hMFm.readLE _ _ htoD, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hto2,
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hs3']
      have hbuf : buf < 2 ^ 64 := by omega
      janus64_run [hsp, hm1, hm2, hs3m, hslot, hn5, BitVec.msb_eq_decide]
      refine hOk _ ⟨by janus64_simp [hsp], by janus64_simp [hm2, regFP], by janus64_simp [h14, regG],
        by janus64_simp [hx15]⟩ ⟨by janus64_simp, by janus64_simp, ?vv⟩
        ⟨by janus64_simp [hfs], by janus64_simp [hdf], Lk, bk, hext, hbud, ?inv, ?held, ?mf, ?lf⟩
      case vv =>
        janus64_simp
        rw [← hd1, beVal_add, beVal_zeros (m := m2) (q := buf) (n := d) fun i hi => ?zz, Nat.zero_mul,
          Nat.zero_add, ← hvv]
        case zz =>
          have hb1 := fresh_byte_out (w := 616) he (by decide) (by decide) hbW (by omega : i < hdrV s p len 2)
          have hb2 := fresh_byte_out (w := 208) he (by decide) (by decide) hbW (by omega : i < hdrV s p len 2)
          have h1 := hLFm.readLE (buf + i) 1 (hBL.sub (by omega) (by omega)) (by
            simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega)
          rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hb1,
            Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ hb2] at h1
          simp only [Janus.Arm64.Memory.readLE_one] at h1
          rw [h1]; exact hBz i (by omega)
        rw [Nat.add_comm buf d]
        apply beVal_congr'
        intro i hi
        rw [hcp i hi]
        have hb1 := fresh_byte_out (w := 616) he (by decide) (by decide) hvw' hi
        have hb2 := fresh_byte_out (w := 208) he (by decide) (by decide) hvw' hi
        have h1 := Janus.Arm64.Memory.readLE_writeLE_of_disjoint
          (U.mem.writeLE ((s.regs 4).toNat - 208) 8 buf) 6639494 hb1
        have h2 := Janus.Arm64.Memory.readLE_writeLE_of_disjoint U.mem buf hb2
        rw [h2, Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at h1
        exact BitVec.eq_of_toNat_eq h1
      case inv => dsimp only; exact hinvm
      case held => janus64_simp; intro _; exact Or.inl hBL
      case mf =>
        dsimp only
        refine (hMF.trans ?w1 fun a n h => ⟨h, outW_w h⟩).trans hMFm fun a n h => ⟨h, outW_csd2 hW hdRt h⟩
        case w1 => exact frame_two_slots _ _ _ _ (by decide) (Nat.le_trans (by decide) hW) (by decide) (Nat.le_trans (by decide) hW) hb'
      case lf =>
        dsimp only
        refine hLF.trans ⟨fun a n hin _ => ?_⟩ (fun _ _ h => h)
        have hin' := hext.inRanges_old hin
        have hU := (LiveFrame.of_win (L := L) (ex := []) (m := U.mem)
          (m' := (U.mem.writeLE ((s.regs 4).toNat - 208) 8 buf).writeLE ((s.regs 4).toNat - 616) 8 6639494)
          (frame_two_slots _ _ _ _ (by decide) (Nat.le_trans (by decide) hW) (by decide) (Nat.le_trans (by decide) hW) hb') (fun r hr => hLsS r (hext.mem_old hr))).readLE a n hin trivial
        rw [← hU]
        refine hLFm.readLE a n hin' ?_
        obtain ⟨r, hr, h1, h2⟩ := hin
        have := hBsep r hr
        simp only [Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; omega

end FvModexp.Amd64.Run
