import FvModexp.Proofs.Amd64.NatQ.DivLessF
import FvModexp.Proofs.Amd64.NatQ.DivOneF
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLessC.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64), `u < v`: `copy(r, u)` (`memmove`, zero-length `memmove` or skipped when `r`'s array is `u`'s),
`r` stored, return (natdiv.go:534-535, nat.go:93-94)

From `joinS` (`fn + 0x28a`): `CMPQ AX, CX; MOVQ CX, SI; CMOVL AX, CX` (`CX = SI = len u`); `R9 = [RSP + 8] = u`;
`CMPQ R9, BX; JE fn + 0x2de` (no copy when `p = u`); spills `SI → SP' + 0x88` (`RSP - 96`), `BX → SP' + 0x90`
(`RSP - 88`), `DX → SP' + 0x78` (`RSP - 112`); `memmove(p, u, 8 len u)` at `fn + 0x2c4` (return `retM = fn + 0x2c9`);
reloads; `r` stored at `SP' + 0x98 … 0xa8` (`RSP - 80 … - 64`); results `q = [RSP - 56 … - 40]`, `r = (BX, SI, DX)`;
`ADDQ $0xe0, SP; POPQ BP; RET` (`fn + 0x320`). Port of `Arm64/Nat/DivLessC.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

/-- `memmove`'s return in the `u < v` copy (`fn + 0x2c9`) -/
abbrev retM : Nat := 0x5ee1e9

theorem copied_sub {m0 m : Janus.Arm64.Memory} {dst src n k l : Nat} (h : Janus.Contracts.Mem.Copied m0 m dst src n)
    (hk : k + l ≤ n) : Janus.Contracts.Mem.Copied m0 m (dst + k) (src + k) l := fun i hi => by
  have := h (k + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

/-- the objects of a grown live set lie outside the window (numeric form) -/
theorem lsepS {R : RtInv} {L L' : List (Nat × Nat)} {s : State} (hce : CallEnv R L s 41512 112)
    (hext : LiveExt R L L') :
    ∀ r ∈ L', r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ r.1 := by
  have hout := hce.2.2.2.2.1
  have hLs := hce.2.2.2.2.2.2.2.1
  obtain ⟨ns, rfl, hn, -⟩ := hext
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  · have := outside_of_inRanges hout (hn r hr).1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `len u > 0`: the postcondition after the `memmove` and the `r` stores (pure) -/
theorem lessC1F {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b H dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u ul s p c L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (hu0 : 0 < ul) (hpw : p + 8 * ul ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ p)
    {M1 m : Janus.Arm64.Memory}
    (hW0 : MemFrame S.mem M1 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 112, (s.regs 4).toNat - 80)])
    (hF2 : MemFrame M1 m (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
      ((s.regs 4).toNat - 240 + 8, (s.regs 4).toNat - 240 + 8 + 24)] ++ [(p, p + 8 * ul)]))
    (hLF2 : LiveFrame M1 m L' [(p, p + 8 * ul)]) (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' m))
    (hcp : Janus.Contracts.Mem.Copied M1 m p u (8 * ul)) (s' : State) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df)
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 0) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 p) (h4 : s'.regs 6 = BitVec.ofNat 64 ul) (h5 : s'.regs 8 = BitVec.ofNat 64 c)
    (hm : s'.mem = ((m.writeLE ((s.regs 4).toNat - 80) 8 p).writeLE ((s.regs 4).toNat - 72) 8 ul).writeLE
      ((s.regs 4).toNat - 64) 8 c) :
    PostLG R b H dc L zp zc st z2 z2c u ul v vl s s' := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, -⟩, -, -, hout, -⟩ := hp.ce
  simp only [regSP] at hb' ha
  have hul := hp.ul9
  obtain ⟨hu40, -, hu48, -, huw⟩ := hp.uo
  simp only [win, outside_cons, outside_nil, and_true] at huw
  have hLs1 := lsepS hce hS.ext
  have rdS : ∀ a n, (a + n ≤ (s.regs 4).toNat - 240 ∨ (s.regs 4).toNat - 80 ≤ a) → M1.readLE a n = S.mem.readLE a n :=
    fun a n h => hW0.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hcpv := FvModexp.Expmc.readLE_of_copied hcp
  have hcpt := FvModexp.Expmc.readLE_of_copied (copied_sub (k := 8 * (ul - 1)) (l := 8) hcp (by omega))
  rw [rdS _ _ (by omega)] at hcpv hcpt
  have har : ar p ul = [(p, p + 8 * ul)] := by unfold ar; rw [if_pos hu0]
  have hW2 : MemFrame m s'.mem [((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)] := by rw [hm]; janus_frame
  clear hce hp
  refine lessFin hpre.toG hS hU _ hfs hdf h0 h1 h2 h3 h4 h5 ?hM ?hLF ?hI ?hV ?hT
  case hM =>
    rw [har]
    refine (hW0.trans hF2 (rs'' := R.rt ++ win s 41512 112 ++ [(p, p + 8 * ul)]) fun a n h => ?_).trans
      hW2 fun a n h => ⟨h, ?_⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨by omega, by omega⟩, ⟨h.1.1, by omega, by omega⟩, h.2⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega
  case hLF =>
    rw [har]
    refine ⟨fun a n hin ho => ?_⟩
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs1 r hr
    rw [hW2.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF2.readLE a n ⟨r, hr, i1, i2⟩ ho]
    exact hW0.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)]) hW2 (fun r hr => ?_) hinv2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hV =>
    rw [← hcpv]
    exact hW2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hT =>
    intro _
    rw [← hcpt]
    exact hW2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
/-- `len u > 0`: `memmove(r, u, 8·len u)` -/
theorem lessC1 (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibDiv.program.link impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b H dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u ul s p c L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (hu0 : 0 < ul) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S (RQG R b H dc L zp zc st z2 z2c u ul v vl s) := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨htg, htr, htw⟩⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  unfold Apart at hga htw
  have hsv := hp.sv
  have hul := hp.ul9
  obtain ⟨hu40, huacc, hu48, huh, huw⟩ := hp.uo
  simp only [win, outside_cons, outside_nil, and_true] at huw
  have harr := hS.arr
  -- `r`'s array: writable, held in `L'`, outside the window, apart from `u`
  have hpa : S.mem.accessible p (8 * ul) true = true ∧ p + 8 * ul ≤ 2 ^ 48 ∧ Held R L' p (8 * ul) ∧
      (p + 8 * ul ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ p) ∧ Apart p (8 * ul) u (8 * ul) := by
    rcases harr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, hc2, h8, h48, hin, hap, hinL, hacc⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hp.z2o.2.1 (by omega)
      have hw2 := (hp.z2o.2.2 (by omega)).1
      simp only [win, outside_cons, outside_nil, and_true] at hw2
      have hap2 := (hp.pw _ _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) (by omega)).1
      unfold Apart at hap2 ⊢
      refine ⟨by rw [hS.mf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ a3 (Nat.le_refl _) (by omega),
        by omega, hS.ext.held (a2.sub (Nat.le_refl _) (by omega)), by omega, by omega⟩
    · have := outside_of_inRanges hout hin
      have hapu := held_apart_fresh huh hap hin
      unfold Apart at hapu ⊢
      refine ⟨Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), by omega,
        Or.inl (hinL.sub (Nat.le_refl _) (by omega)), by omega, by omega⟩
  obtain ⟨hpacc, hp48, hph, hpw, hpu⟩ := hpa
  have hph' : InRanges p (8 * ul) L' ∨ Outside p (8 * ul) R.rt := hph
  unfold Apart at hpu
  have hacc := hS.mf.accessible
  have huacc' : S.mem.accessible u (8 * ul) false = true := by rw [hacc]; exact huacc
  have hok : R.ok (cA "runtime.memmove") [p, u, 8 * ul] := hsv.2.1 _ _ _ (by omega)
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr3 := hS.r3
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by rw [hacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hS.mf.readLE _ _ (by
      simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hS.mf.readLE _ _ (by simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨htr, by omega⟩)]
    exact htg.g
  have hTt : S.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hacc]; exact htg.readable
  have hLs1 := lsepS hce hS.ext
  have hinvS := hS.inv
  have m0 := hS.ra; have m1 := hS.bp; have m3 := hS.q0; have m4 := hS.q1; have m5 := hS.q2; have m6 := hS.s8
  have hc40 : c < 2 ^ 40 := by
    rcases harr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, hc2, -⟩
    · exact hp.z2o.1
    · omega
  have hzp : zp < 2 ^ 64 := by rw [← hS.q0]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.q2]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hB : Box (Pre R b H dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s ∧ AtS R b L zp zc z2 z2c u ul s p c L' b' S) :=
    ⟨⟨hpre, hS⟩⟩
  clear hpre hp hS hce harr hLs
  have hne : (BitVec.ofNat 64 u = BitVec.ofNat 64 p) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hne1 : ((18446744073709551616 - p + u) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; omega
  have hne2 : ((18446744073709551616 - u + p) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; omega
  have hsh : BitVec.ofNat 64 ul <<< 3 = BitVec.ofNat 64 (8 * ul) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft]; simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  janus64_run [m6, hne, hne1, hne2, hsh, hgS, htS, ite_self, BitVec.msb_eq_decide] until [retM] calls [hmv L' b']
  rename_i m _ _ hF2 hLF2 hinv2 hcp
  generalize hG : ((((S.mem.writeLE ((s.regs 4).toNat - 96) 8 ul).writeLE ((s.regs 4).toNat - 88) 8 p).writeLE
      ((s.regs 4).toNat - 112) 8 c).writeLE ((s.regs 4).toNat - 240) 8 6218217) = M1 at hF2 hLF2 hcp
  have hW0 : MemFrame S.mem M1 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 112, (s.regs 4).toNat - 80)] := by rw [← hG]; janus_frame
  have rd : ∀ a n, (s.regs 4).toNat - 208 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → m.readLE a n = M1.readLE a n :=
    fun a n h1 h2 => hF2.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have rdS : ∀ a n, (a + n ≤ (s.regs 4).toNat - 240 ∨ (s.regs 4).toNat - 80 ≤ a) → M1.readLE a n = S.mem.readLE a n :=
    fun a n h => hW0.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have r0 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m0)
  have r1 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m1)
  have r3 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m3)
  have r4 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m4)
  have r5 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m5)
  have q1 : m.readLE ((s.regs 4).toNat - 96) 8 = ul := by
    rw [rd _ _ (by omega) (by omega), ← hG]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    exact Nat.mod_eq_of_lt (by omega)
  have q2 : m.readLE ((s.regs 4).toNat - 88) 8 = p := by
    rw [rd _ _ (by omega) (by omega), ← hG]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    exact Nat.mod_eq_of_lt (by omega)
  have q3 : m.readLE ((s.regs 4).toNat - 112) 8 = c := by
    rw [rd _ _ (by omega) (by omega), ← hG]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    exact Nat.mod_eq_of_lt (by omega)
  have hra1 : M1.readLE ((s.regs 4).toNat - 240) 8 = 6218217 := by
    rw [← hG, Janus.Arm64.Memory.readLE_writeLE_self]
  janus64_run [hra1, r0, r1, r3, r4, r5, q1, q2, q3]
  obtain ⟨hpre, hS⟩ := hB.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lessC1F hpre hS hU hu0 hpw hW0 hF2 hLF2 hinv2 hcp _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl⟩
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hx15.trans hx0.symm
    | exact hfs
    | (rw [hdf0]; rfl)
    | exact hdf.trans hdf0.symm
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `len u = 0`: the postcondition after the (empty or skipped) copy and the `r` stores (pure) -/
theorem lessC0F {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u uc v vl vc : Nat} {s : State}
    (hpre : PreG R b H dc L zp zl zc st z2 z2l z2c u 0 uc v vl vc s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u 0 s p c L' b' S) (hU : natVal s.mem u 0 < natVal s.mem v vl)
    {M1 m : Janus.Arm64.Memory}
    (hW0 : MemFrame S.mem M1 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 112, (s.regs 4).toNat - 80)])
    (hF2 : MemFrame M1 m (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
      ((s.regs 4).toNat - 240 + 8, (s.regs 4).toNat - 240 + 8 + 24)]))
    (hLF2 : LiveFrame M1 m L' []) (hinv2 : R.inv b' L' (s.regs 14).toNat (view R.rt L' m))
    (s' : State) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 0) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 p) (h4 : s'.regs 6 = BitVec.ofNat 64 0) (h5 : s'.regs 8 = BitVec.ofNat 64 c)
    (hm : s'.mem = ((m.writeLE ((s.regs 4).toNat - 80) 8 p).writeLE ((s.regs 4).toNat - 72) 8 0).writeLE
      ((s.regs 4).toNat - 64) 8 c) :
    PostLG R b H dc L zp zc st z2 z2c u 0 v vl s s' := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, -⟩, -, -, hout, -⟩ := hp.ce
  simp only [regSP] at hb' ha
  have hLs1 := lsepS hce hS.ext
  have har : ar p 0 = [] := rfl
  have hW2 : MemFrame m s'.mem [((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)] := by rw [hm]; janus_frame
  clear hce hp
  refine lessFin hpre hS hU _ hfs hdf h0 h1 h2 h3 h4 h5 ?hM ?hLF ?hI ?hV (fun h => absurd h (by omega))
  case hM =>
    rw [har]
    rw [List.append_nil]
    refine (hW0.trans hF2 (rs'' := R.rt ++ win s 41512 112) fun a n h => ?_).trans
      hW2 fun a n h => ⟨h, ?_⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨by omega, by omega⟩, h.1, by omega, by omega⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega
  case hLF =>
    rw [har]
    refine ⟨fun a n hin ho => ?_⟩
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs1 r hr
    rw [hW2.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF2.readLE a n ⟨r, hr, i1, i2⟩ ho]
    exact hW0.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)]) hW2 (fun r hr => ?_) hinv2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hV => simp only [Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
/-- `len u = 0`: `memmove(r, u, 0)` (zero-length contract) or skipped (`r`'s pointer = `u`'s) -/
theorem lessC0 (impl : List Amd64.Segment) (R : RtInv)
    (hmz : MemmoveZeroLive64 (LibDiv.program.link impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u uc v vl vc : Nat} {s : State}
    (hpre : PreG R b H dc L zp zl zc st z2 z2l z2c u 0 uc v vl vc s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u 0 s p c L' b' S) (hU : natVal s.mem u 0 < natVal s.mem v vl)
    (hz2 : z2 < 2 ^ 64) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128)
    (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S (RQG R b H dc L zp zc st z2 z2c u 0 v vl s) := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨htg, htr, htw⟩⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  unfold Apart at hga htw
  have hsv := hp.sv
  have hok : ∀ d sr, R.ok (cA "runtime.memmove") [d, sr, 0] := fun d sr => hsv.2.1 _ _ _ (by omega)
  have hacc := hS.mf.accessible
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2; have hr3 := hS.r3
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by rw [hacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hS.mf.readLE _ _ (by
      simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hS.mf.readLE _ _ (by simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨htr, by omega⟩)]
    exact htg.g
  have hTt : S.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hacc]; exact htg.readable
  have hLs1 := lsepS hce hS.ext
  have hinvS := hS.inv
  have m0 := hS.ra; have m1 := hS.bp; have m3 := hS.q0; have m4 := hS.q1; have m5 := hS.q2; have m6 := hS.s8
  have hc40 : c < 2 ^ 40 := by
    rcases hS.arr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, hc2, -⟩
    · exact hp.z2o.1
    · omega
  have hp64 : p < 2 ^ 64 := by
    rcases hS.arr with ⟨rfl, -⟩ | ⟨-, -, -, -, h48, -⟩
    · exact hz2
    · omega
  have hu64 : u < 2 ^ 64 := by rw [← hS.s8]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := by rw [← hS.q0]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.q2]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hB : Box (PreG R b H dc L zp zl zc st z2 z2l z2c u 0 uc v vl vc s ∧ AtS R b L zp zc z2 z2c u 0 s p c L' b' S) :=
    ⟨⟨hpre, hS⟩⟩
  clear hpre hp hS hce hLs
  by_cases hpu : BitVec.ofNat 64 u = BitVec.ofNat 64 p
  · have hpu2 : u = p := by
      have := congrArg BitVec.toNat hpu; simp only [BitVec.toNat_ofNat] at this; omega
    subst hpu2
    janus64_run [m0, m1, m3, m4, m5, m6, ite_self, BitVec.msb_eq_decide]
    obtain ⟨hpre, hS⟩ := hB.h
    refine ⟨⟨?_, ?_, ?_, ?_⟩, lessC0F hpre hS hU (MemFrame.refl _ _) (MemFrame.refl _ _) (LiveFrame.refl _ _ _)
      hinvS _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl⟩
    all_goals try (janus64_simp; done)
    all_goals first
      | exact hx15.trans hx0.symm
      | exact hfs
      | (rw [hdf0]; rfl)
      | exact hdf.trans hdf0.symm
      | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)
  · have hne := eq_false hpu
    have hne1 : ((18446744073709551616 - p + u) % 18446744073709551616 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; apply hpu
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
    janus64_run [m6, hne, hne1, hgS, htS, ite_self, BitVec.msb_eq_decide] until [retM] calls [hmz L' b']
    rename_i m _ _ hLF2 _ hF2 hinv2
    generalize hG : ((((S.mem.writeLE ((s.regs 4).toNat - 96) 8 0).writeLE ((s.regs 4).toNat - 88) 8 p).writeLE
        ((s.regs 4).toNat - 112) 8 c).writeLE ((s.regs 4).toNat - 240) 8 6218217) = M1 at hF2 hLF2
    have hW0 : MemFrame S.mem M1 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
        ((s.regs 4).toNat - 112, (s.regs 4).toNat - 80)] := by rw [← hG]; janus_frame
    have rd : ∀ a n, (s.regs 4).toNat - 208 ≤ a → a + n ≤ (s.regs 4).toNat + 112 → m.readLE a n = M1.readLE a n :=
      fun a n h1 h2 => hF2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)
    have rdS : ∀ a n, (a + n ≤ (s.regs 4).toNat - 240 ∨ (s.regs 4).toNat - 80 ≤ a) →
        M1.readLE a n = S.mem.readLE a n :=
      fun a n h => hW0.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
    have r0 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m0)
    have r1 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m1)
    have r3 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m3)
    have r4 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m4)
    have r5 := (rd _ _ (by omega) (by omega)).trans ((rdS _ _ (by omega)).trans m5)
    have q1 : m.readLE ((s.regs 4).toNat - 96) 8 = 0 := by
      rw [rd _ _ (by omega) (by omega), ← hG]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
    have q2 : m.readLE ((s.regs 4).toNat - 88) 8 = p := by
      rw [rd _ _ (by omega) (by omega), ← hG]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
      exact Nat.mod_eq_of_lt (by omega)
    have q3 : m.readLE ((s.regs 4).toNat - 112) 8 = c := by
      rw [rd _ _ (by omega) (by omega), ← hG]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
      exact Nat.mod_eq_of_lt (by omega)
    have hra1 : M1.readLE ((s.regs 4).toNat - 240) 8 = 6218217 := by
      rw [← hG, Janus.Arm64.Memory.readLE_writeLE_self]
    janus64_run [hra1, r0, r1, r3, r4, r5, q1, q2, q3]
    obtain ⟨hpre, hS⟩ := hB.h
    refine ⟨⟨?_, ?_, ?_, ?_⟩, lessC0F hpre hS hU hW0 hF2 hLF2 hinv2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl⟩
    all_goals try (janus64_simp; done)
    all_goals first
      | exact hx15.trans hx0.symm
      | exact hfs
      | (rw [hdf0]; rfl)
      | exact hdf.trans hdf0.symm
      | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)

end FvModexp.Amd64.Q.NatDiv
