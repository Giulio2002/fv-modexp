import FvModexp.Proofs.Arm64.Nat.DrsFin
import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivLargeCallees
import FvModexp.Proofs.Common.DivmcNat

/-!
# `divRecursiveStep` (arm64): `n < divRecursiveThreshold` → `z.divBasic(stk, u, v)` (natdiv.go:762-765)

`dbsumS`: `divBasic`'s `ens` as a summary on `LibDrs`; `raS`: a return site inside `divRecursiveStep`'s segment;
`db_preS`: `DivBasic.Pre` at the call (one frame of 400 below the entry, memory changed only in the own frame `fw s`);
`db_postS`: `DivBasic.Post` → `DrsPostW` (`q[qn:]` and `u[len u':len u]` keep their zeros); `pathB`: the run.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the callee's call environment one frame (`f` bytes) down (adapted from fv-modexp divmc's `NatMul.callEnv_shift`,
Arm64/Nat/MulOps.lean) -/
theorem callEnv_shift {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W ab))
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hg : S1.regs 28 = s.regs 28) (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 + 8 ≤ f) (hab : 8 ≤ ab) (hf16 : f % 16 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  unfold Apart at hga
  have hgr' : S1.mem.readLE ((S1.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hF1.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hF1.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact dataLoaded_win hdl hreg hro hF1 hw (by
      intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega

set_option linter.defProp false in
/-- `divBasic`'s `ens` as a summary in `LibDrs.program.link impl` -/
def dbsumS (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (qp ql qc st up ul uc vp vl vc : BitVec 64) :=
  Ensures.toSummaryIn (DivBasic.ens impl hap R hgr hmc hwb b L qp ql qc st up ul uc vp vl vc)
    (noExit_restrict hap DivBasic.names)
    (show CodeIn ((Extracted.program.onlySegments DivBasic.names).link impl) (LibDrs.program.link impl) by
      rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide)))

set_option maxRecDepth 20000 in
/-- a return site inside `divRecursiveStep`'s segment is admissible for a callee program that does not keep it -/
theorem raS (impl : List Segment) (hap : ImplApart Extracted.program impl) (ns : List String)
    (hn : ns.contains fn = false) (ret : Nat) (hal : ret % 4 = 0) (h1 : 0x1ba3a0 ≤ ret) (h2 : ret < 0x1ba3a0 + 4 * 669)
    (hst : ∀ st ∈ Extracted.program.stubs, st.addr ≠ ret) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) ret := by
  have hmem : Extracted.seg45 ∈ Extracted.program.segments := by
    have : Extracted.program.segments[45]'(by decide) = Extracted.seg45 := rfl
    rw [← this]; exact List.getElem_mem _
  have hb : Extracted.seg45.base = 0x1ba3a0 := rfl
  have hl : Extracted.seg45.words.length = 669 := rfl
  have hnm : Extracted.seg45.name = fn := rfl
  refine RetAddr.of_placement hal (by omega) ⟨_, hmem, by rw [hb]; omega, by rw [hb, hl]; omega⟩ hap.1 ?_ hst
  intro seg hm hc
  by_cases he : seg = Extracted.seg45
  · subst he; rw [hnm, hn] at hc; exact absurd hc (by decide)
  · have hpw := (List.pairwise_append.1 hap.1).1
    have := FvModexp.Arm64.DivLarge.pw_forall (fun {a b} h => by unfold Segment.Apart at h ⊢; omega) hpw hm hmem he
    unfold Segment.Apart at this; rw [hb, hl] at this; omega

/-- the room condition of `divBasic`: the normalised `u` has at most `len v + len q` words and `U < V·B^(len q)` -/
theorem room_drs {U V ul vl ql : Nat} (hv : 1 ≤ vl) (hV : 2 ^ (64 * (vl - 1)) * 2 ^ 63 ≤ V)
    (hU2 : 2 * U < 2 ^ (64 * (vl + ql))) (hUn : ul = 0 ∨ 2 ^ (64 * (ul - 1)) ≤ U) :
    vl ≤ ul → (ul - vl < ql ∨ (ul - vl = ql ∧ U < V * 2 ^ (64 * ql))) := by
  intro hvu
  have e : 2 ^ (64 * (vl + ql)) = 2 * (2 ^ (64 * (vl - 1)) * 2 ^ 63 * 2 ^ (64 * ql)) := by
    rw [show 64 * (vl + ql) = 1 + (64 * (vl - 1) + 63 + 64 * ql) by omega, Nat.pow_add, Nat.pow_add, Nat.pow_add,
      Nat.pow_one]
  have hlt : U < V * 2 ^ (64 * ql) :=
    Nat.lt_of_lt_of_le (by rw [e] at hU2; omega) (Nat.mul_le_mul_right _ hV)
  have hle : ul ≤ vl + ql := by
    rcases hUn with h | h
    · omega
    · refine Nat.le_of_not_lt fun hc => ?_
      have : 2 ^ (64 * (vl + ql)) ≤ 2 ^ (64 * (ul - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  rcases Nat.lt_or_ge (ul - vl) ql with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by omega, hlt⟩

/-- the top word of `v` bounds `V` from below -/
theorem v_ge {M : Memory} {vp vl : Nat} (hv : 1 ≤ vl) (htop : 2 ^ 63 ≤ M.readLE (vp + 8 * (vl - 1)) 8) :
    2 ^ (64 * (vl - 1)) * 2 ^ 63 ≤ natVal M vp vl := by
  have h := natVal_add M vp (vl - 1) 1
  rw [show vl - 1 + 1 = vl by omega] at h
  have h1 : natVal M (vp + 8 * (vl - 1)) 1 = M.readLE (vp + 8 * (vl - 1)) 8 := rfl
  rw [h, h1]
  have := Nat.mul_le_mul_left (2 ^ (64 * (vl - 1))) htop
  omega

/-- `StkOK` with the header unchanged (adapted from fv-modexp divmc's `NatMul.stkOK_move`, Arm64/Nat/MulOps.lean) -/
theorem stkOK_moveS {R : RtInv} {L : List (Nat × Nat)} {m m' : Memory} {st : Nat} (h : StkOK m R L st)
    (eW : stW m' st = stW m st) (eL : stLen m' st = stLen m st) (eC : stCap m' st = stCap m st)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : StkOK m' R L st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, by rw [hacc]; exact h3, h4, ?_, by rw [eL, eC]; exact h6, by rw [eC]; exact h7⟩
  rw [eW, eC]; intro hc; obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, q2, by rw [hacc]; exact q3, q4⟩

set_option maxHeartbeats 8000000 in
/-- **`DivBasic.Pre` at the call** (`X`: one frame of 400 below the entry, memory = the entry's up to the own frame) -/
theorem db_preS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X : State} {ul' : Nat} (hpre : DrsPreW R b L c W qp ql qc st up ul uc vp vl vc s) (hW : 4864 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : X.sp = s.sp - 400#64) (h28 : X.regs 28 = s.regs 28)
    (hreg : X.mem.regions = s.mem.regions) (hle : ul' ≤ ul) (hU : natVal s.mem up ul' = natVal s.mem up ul)
    (hN : NatNorm s.mem up ul') (hcost : stackNatCost (stLen s.mem st) (vl + 1) ≤ b) :
    DivBasic.Pre R b L qp ql st up ul' uc vp vl X := by
  obtain ⟨hce, hsv, hgl, hqlc, hqc, hulc, huc, hvlc, hvc, hv2, ⟨hvl9, hql9⟩, htop, -, hU2,
    ⟨hqa, hq48, hqh, hqo, hqg⟩, ⟨hua, hu48, huh, huo, hug⟩, ⟨hva, hv48, hvh, hvo, -, -, -⟩, hqu, hqv, huv,
    hsti, ⟨hstl, hcap0, -⟩, ⟨hqs, hqf⟩, ⟨hus, huf⟩, ⟨hvs, hvf⟩, hswb, hsf, hfo, -, -, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce'
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF.accessible a n w
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  obtain ⟨hok, hstw, hstg, harr⟩ := hsti
  have hsw : Outside st 24 (win s W 96) := hstw
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hsw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have hlc := hok.2.2.2.2.2.1
  have hF1 : MemFrame s.mem X.mem (R.rt ++ winA s W 96) := hF.mono fun a n ho => by
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho
    simp only [fw, winA, outside_cons, outside_nil, and_true]; omega
  have hvt : 2 ^ 63 ≤ X.mem.readLE (vp + 8 * (vl - 1)) 8 := by
    rw [rdX _ _ (hvo.of_sub (by omega) (by omega))]; exact htop
  have hUX0 : X.mem.readLE up (8 * ul') = s.mem.readLE up (8 * ul') :=
    rdX _ _ (huo.of_sub (Nat.le_refl _) (by omega))
  have hUX : natVal X.mem up ul' = natVal s.mem up ul := hUX0.trans hU
  have hVX : natVal X.mem vp vl = natVal s.mem vp vl := rdX _ _ hvo
  have hroom := room_drs (U := natVal s.mem up ul) (V := natVal s.mem vp vl) (ul := ul') (vl := vl) (ql := ql)
    (by omega) (v_ge (by omega) htop) hU2 (by
      rcases Nat.eq_zero_or_pos ul' with h0 | h0
      · exact Or.inl h0
      rcases hN with h | h
      · exact Or.inl h
      · right; rw [← hU]; exact natVal_ge _ _ _ h0 h)
  have hwin : ∀ a n, Outside a n (win s W 96) → Outside a n (win X 4464 88) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hspn]; omega
  have hwb := hgl.2.2.2.2.2.2.2.2.2.2.1
  unfold DivBasic.Pre
  refine ⟨callEnv_shift hce hLs hF1 hspn h28 hreg (by omega) (by omega) (by omega) (by omega), hsv,
    by rw [hXacc]; exact hwb, hswb, hv2, hvt, by rw [hXacc]; exact hva, hv48, hvh, hwin _ _ hvo, by omega, by omega, huc,
    by rw [hXacc]; exact Memory.accessible_mono _ hua (Nat.le_refl _) (by omega), by omega,
    huh.sub (Nat.le_refl _) (by omega), hwin _ _ (huo.of_sub (Nat.le_refl _) (by omega)),
    by rw [h28]; unfold Apart at hug ⊢; omega, by omega, by rw [hXacc]; exact hqa, hq48, hqh, hwin _ _ hqo,
    by rw [h28]; exact hqg, by unfold Apart at hqu ⊢; omega, hqv, by unfold Apart at huv ⊢; omega,
    by rw [hUX, hVX]; exact hroom, stkOK_moveS hok eW eL eC hXacc, hwin _ _ hsw, by rw [h28]; exact hstg, ?starr,
    ?stgf, by rw [eL]; omega, by unfold Apart at hqs ⊢; omega, by unfold Apart at hus ⊢; omega,
    by unfold Apart at hvs ⊢; omega, ?free, by simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; exact hsf,
    by simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; exact hwin _ _ hfo, by rw [eL]; exact hcost,
    by rw [h28]; exact RtInv.inv_frame' hF (fun r hr => by
      simp only [fw, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by simp only; omega) (by simp only; omega))) hinv⟩
  case starr =>
    rw [eW, eC, h28]; intro hc; obtain ⟨h1, h2⟩ := harr hc; exact ⟨hwin _ _ h1, h2⟩
  case stgf =>
    simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; rw [h28]
    obtain ⟨-, h2⟩ := harr hcap0
    unfold Apart at h2 ⊢; omega
  case free =>
    simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]
    refine ⟨?_, ?_, ?_⟩ <;> unfold Apart at hqf huf hvf ⊢ <;> omega

theorem qn_le (ql ul vl : Nat) : DivBasic.qn ql ul vl ≤ ql := by
  simp only [DivBasic.qn]; split <;> omega

/-- the high part of a zero value is zero -/
theorem natVal_hi_zero {M : Memory} {p n k : Nat} (hk : k ≤ n) (h : natVal M p n = 0) :
    natVal M (p + 8 * k) (n - k) = 0 := by
  have e := natVal_add M p k (n - k)
  rw [show k + (n - k) = n by omega, h] at e
  have := Nat.two_pow_pos (64 * k)
  rcases Nat.eq_zero_or_pos (natVal M (p + 8 * k) (n - k)) with h0 | h0
  · exact h0
  · have := Nat.mul_le_mul (Nat.succ_le_of_lt this) (Nat.succ_le_of_lt h0); omega

set_option maxHeartbeats 16000000 in
/-- **`DivBasic.Post` → `DrsPostW`** (pure) -/
theorem db_postS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X T : State} {ul' : Nat} (hpre : DrsPreW R b L c W qp ql qc st up ul uc vp vl vc s) (hW : 4864 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : X.sp = s.sp - 400#64) (h28 : X.regs 28 = s.regs 28)
    (hle : ul' ≤ ul) (hU : natVal s.mem up ul' = natVal s.mem up ul)
    (hc : c = ExpHyp.stackNatCost (stLen s.mem st) (vl + 1))
    (hpost : DivBasic.Post R b L qp ql st up ul' vp vl X T) :
    DrsPostW R b L c W qp ql st up ul vp vl s T := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, hv2, -, htop, hq0, -,
    ⟨-, hq48, hqh, hqo, -⟩, ⟨-, hu48, huh, huo, -⟩, ⟨-, -, -, hvo, -, -, -⟩, hqu, -, -,
    hsti, -, ⟨hqs, hqf⟩, ⟨hus, huf⟩, -, -, -, -, -, -, -⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce'
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  obtain ⟨hok, hstw, -, -⟩ := hsti
  have hsw : Outside st 24 (win s W 96) := hstw
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hsw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have hlc := hok.2.2.2.2.2.1
  obtain ⟨hqv, hrv, L', b', hx, hb, hinv, hSB, hMF, hLF⟩ := hpost
  simp only [DivBasic.ws, stkWs, eW, eL, eC] at hMF hLF
  rw [eL, ← hc] at hb
  rw [h28] at hinv
  have hUX0 : X.mem.readLE up (8 * ul') = s.mem.readLE up (8 * ul') :=
    rdX _ _ (huo.of_sub (Nat.le_refl _) (by omega))
  have hUX : natVal X.mem up ul' = natVal s.mem up ul := hUX0.trans hU
  have hVX : natVal X.mem vp vl = natVal s.mem vp vl := rdX _ _ hvo
  rw [hUX, hVX] at hqv hrv
  have hqn := qn_le ql ul' vl
  generalize hk : DivBasic.qn ql ul' vl = k at hqv hMF hLF hqn
  -- reads kept from `X` to `T`: held, outside the window, the written ranges
  have rdT : ∀ a n, Held R L a n → Outside a n (win s W 96) → a + n ≤ qp ∨ qp + 8 * k ≤ a →
      Apart a n up (8 * ul') → Apart a n st 24 →
      Apart a n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) →
      T.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh ho hq hu hs hf
    rw [FvModexp.Expmc.held_readLE (ws1 := winA X 4464 88) hh hMF hLF ?_ ?_]
    · exact rdX a n ho
    · simp only [win, winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
    · simp only [outside_cons, outside_nil, and_true]; unfold Apart at hu hs hf; omega
  have hqz : natVal s.mem qp ql = 0 := hq0
  refine ⟨?_, ?_, L', b', ⟨hx, hb, hinv⟩, ?_, ?_, ?_⟩
  · -- `q`: `q[0:k]` = U/V, `q[k:]` kept (zero)
    have hhi : natVal T.mem (qp + 8 * k) (ql - k) = 0 := by
      rw [← natVal_hi_zero hqn hqz]; unfold natVal
      refine rdT _ _ (hqh.sub (by omega) (by omega)) (hqo.of_sub (by omega) (by omega)) (Or.inr (by omega)) ?_ ?_ ?_
      · unfold Apart at hqu ⊢; omega
      · unfold Apart at hqs ⊢; omega
      · unfold Apart at hqf ⊢; omega
    have e := natVal_add T.mem qp k (ql - k)
    rw [show k + (ql - k) = ql by omega, hhi, Nat.mul_zero, Nat.add_zero] at e
    rw [e]
    by_cases hvu : vl ≤ ul'
    · exact hqv hvu
    · have hk0 : k = 0 := by rw [← hk]; simp only [DivBasic.qn]; rw [if_neg hvu]
      subst hk0
      have := u_lt_v (M := s.mem) (by omega) htop (by omega : ul' < vl) hU
      rw [Nat.div_eq_of_lt this]; rfl
  · -- `u`: `u[0:ul']` = U mod V, `u[ul':ul]` kept (zero)
    have hhi0 : natVal s.mem (up + 8 * ul') (ul - ul') = 0 := by
      have e := natVal_add s.mem up ul' (ul - ul')
      rw [show ul' + (ul - ul') = ul by omega, ← hU] at e
      have := Nat.two_pow_pos (64 * ul')
      rcases Nat.eq_zero_or_pos (natVal s.mem (up + 8 * ul') (ul - ul')) with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul (Nat.succ_le_of_lt this) (Nat.succ_le_of_lt h0); omega
    have hhi : natVal T.mem (up + 8 * ul') (ul - ul') = 0 := by
      rw [← hhi0]; unfold natVal
      refine rdT _ _ (huh.sub (by omega) (by omega)) (huo.of_sub (by omega) (by omega)) ?_ (by unfold Apart; omega) ?_ ?_
      · unfold Apart at hqu; omega
      · unfold Apart at hus ⊢; omega
      · unfold Apart at huf ⊢; omega
    have e := natVal_add T.mem up ul' (ul - ul')
    rw [show ul' + (ul - ul') = ul by omega, hhi, Nat.mul_zero, Nat.add_zero] at e
    rw [e]; exact hrv
  · obtain ⟨hok', hlen, hor⟩ := hSB
    refine ⟨hok', by rw [hlen, eL], ?_⟩
    rw [eW, eC] at hor; exact hor
  · refine hF.trans hMF fun a n ho => ⟨?_, ?_⟩
    · simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho
      simp only [fw, winA, outside_cons, outside_nil, and_true]
      omega
    · have hrt : Outside a n R.rt := by simp only [outside_append] at ho; exact ho.1.1.1
      simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
      simp only [hrt, true_and]
      rw [hspn]; omega
  · refine ⟨fun a n hin ho => ?_⟩
    simp only [List.cons_append, outside_cons, List.nil_append, outside_nil, and_true] at ho
    rw [hLF.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; omega)]
    refine hF.readLE a n ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at this ⊢
    omega

set_option maxHeartbeats 8000000 in
/-- the caller's saved `FP`/`LR` slots (and accessibility) survive the `divBasic` call -/
theorem db_slot {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X T : State} {ul' : Nat} (hpre : DrsPreW R b L c W qp ql qc st up ul uc vp vl vc s) (hW : 4864 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : X.sp = s.sp - 400#64) (hle : ul' ≤ ul)
    (hpost : DivBasic.Post R b L qp ql st up ul' vp vl X T) {a n : Nat} (h1 : s.sp.toNat - 408 ≤ a)
    (h2 : a + n ≤ s.sp.toNat - 392) :
    T.mem.readLE a n = X.mem.readLE a n ∧ ∀ a n w, T.mem.accessible a n w = s.mem.accessible a n w := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqo, -⟩, ⟨-, -, -, huo, -⟩, -, -, -, -,
    ⟨-, hstw, -, -⟩, -, -, -, -, -, -, hfo, -, -, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  have hsw : Outside st 24 (win s W 96) := hstw
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hsw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  obtain ⟨-, -, L2, b2, -, -, -, -, hMF, -⟩ := hpost
  have hqn := qn_le ql ul' vl
  simp only [DivBasic.ws, stkWs, eW, eL, eC] at hMF
  generalize DivBasic.qn ql ul' vl = k at hMF hqn
  simp only [win, outside_cons, outside_nil, and_true] at hqo huo hsw hfo
  refine ⟨hMF.readLE a n ?_, fun a n w => by rw [hMF.accessible, hF.accessible]⟩
  rw [outside_append, outside_append]
  refine ⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, ?_⟩
  · simp only [winA, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega

end FvModexp.Arm64.DivRec
