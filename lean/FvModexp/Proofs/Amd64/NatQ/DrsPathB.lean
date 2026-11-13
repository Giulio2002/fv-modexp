import FvModexp.Proofs.Amd64.NatQ.DrsAt
import FvModexp.Proofs.Amd64.NatQ.DrsFin
import FvModexp.Proofs.Amd64.NatQ.DivBasic
import FvModexp.Proofs.Amd64.Nat.Callees
import FvModexp.Proofs.Common.DivmcNat

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): `n < divRecursiveThreshold` → `z.divBasic(stk, u, v)` (natdiv.go:762-765), the pure part

Twin of Arm64/NatQ/DrsPathB.lean. `dbsum`: top's `Q.DivBasic.ensL` as a summary on `LibDrs`; `raB`: the return site
`0x5efa1b` (inside `divRecursiveStep`, `seg45`) is admissible for `divBasic`'s program; `db_pre`: `Q.DivBasic.Pre` at the
call (callee entry `RSP = r - 400`, memory = the entry's up to the own frame `fw s`, `v` stored at `r - 392 / - 384`);
`db_post`: `Q.DivBasic.PostL` → `DrsPostW`; `db_slot`: the caller's slots above the callee window survive the call.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface (Serves)
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem drsB_pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hR _ _ (hp.1 a ha')
      · exact drsB_pairwise_ne hR hp.2 ha' hb' hne

theorem drsB_find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact drsB_find_none_of h x hx'

theorem drsB_retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
    {ns : List String} {cs : Amd64.Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat)
    (hi : i < cs.bytes.length) (hu : cs.base + i < 2 ^ 47) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + i) := by
  refine ⟨hu, fun seg hseg => ?_, fun st hst => ?_⟩
  · have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have hne : seg ≠ cs := by
      rintro rfl
      rcases List.mem_append.1 hseg with h | h
      · have := (List.mem_filter.1 h).2
        rw [hn] at this; exact absurd this (by decide)
      · have := hap.1
        rw [List.pairwise_append] at this
        have := this.2.2 seg hcs seg h
        unfold Amd64.Segment.Apart at this
        omega
    have := drsB_pairwise_ne (fun a b h => by unfold Amd64.Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Amd64.Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Amd64.Program.stubAt at h1
    have := drsB_find_none_of h1 st hst
    simp at this
    exact this

set_option maxRecDepth 20000 in
/-- the return site `0x5efa1b` (after `CALL nat.divBasic`) is admissible for `divBasic`'s program -/
theorem raB (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments FvModexp.Amd64.DivBasic.names).link impl) 0x5efa1b := by
  have := drsB_retAddr_restrict hap (cs := Extracted.seg45) (ns := FvModexp.Amd64.DivBasic.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by decide) 0x19b (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option linter.defProp false in
/-- `divBasic`'s `ensL` as a summary in `LibDrs.program.link impl` (register arguments read at the call) -/
def dbsum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (vp vl : Nat) :=
  FvModexp.Amd64.Callees.Ensures.toSummaryRegs7 (fun a0 a1 a2 a3 a4 a5 a6 =>
    Q.DivBasic.ensL impl hap R hgr hmc hwb H b L a0 a1 a2 a3 a4 a5 a6 vp vl)
    (A64.noExit_restrict64 hap FvModexp.Amd64.DivBasic.names)
    (show CodeIn64 ((Extracted.program.onlySegments FvModexp.Amd64.DivBasic.names).link impl) (LibDrs.program.link impl) by
      rw [LibDrs.eq_only]; exact A64.codeIn_restrict_mono64 hap (FvModexp.Amd64.Callees.sub_of_all (by decide)))

/-- the callee's call environment one frame (`f` bytes) down (= divmc's `Q.NatMul.callEnv_shift`,
Amd64/NatQ/MulOps.lean, restated so that drs does not import the multiplication modules) -/
theorem callEnv_shiftB {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ win s W ab))
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 ≤ f + ab) (hf8 : f % 8 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgr' : S1.mem.readLE ((S1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  have htls : S1.mem.readLE (S1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨htrt, by omega⟩)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF1.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF1.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro hF1 (by
      intro r hr _; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · rw [hg]; exact hgr
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega
  · rw [hfs]; exact htb
  · rw [hfs, hF1.accessible]; exact htr
  · rw [htls, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

/-- `StkOK` with the header unchanged (= divmc's `Q.NatMul.stkOK_move`, Amd64/NatQ/MulOps.lean) -/
theorem stkOK_moveB {R : RtInv} {L : List (Nat × Nat)} {m m' : Memory} {st : Nat} (h : StkOK m R L st)
    (eW : stW m' st = stW m st) (eL : stLen m' st = stLen m st) (eC : stCap m' st = stCap m st)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : StkOK m' R L st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, by rw [hacc]; exact h3, h4, ?_, by rw [eL, eC]; exact h6, by rw [eC]; exact h7⟩
  rw [eW, eC]; intro hc; obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, q2, by rw [hacc]; exact q3, q4⟩

/-- the room condition of `divBasic` (= arm64 NatQ/DrsPathB `room_drs`) -/
theorem room_drsB {U V ul vl ql : Nat} (hv : 1 ≤ vl) (hV : 2 ^ (64 * (vl - 1)) * 2 ^ 63 ≤ V)
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
theorem v_geB {M : Memory} {vp vl : Nat} (hv : 1 ≤ vl) (htop : 2 ^ 63 ≤ M.readLE (vp + 8 * (vl - 1)) 8) :
    2 ^ (64 * (vl - 1)) * 2 ^ 63 ≤ natVal M vp vl := by
  have h := natVal_add M vp (vl - 1) 1
  rw [show vl - 1 + 1 = vl by omega] at h
  have h1 : natVal M (vp + 8 * (vl - 1)) 1 = M.readLE (vp + 8 * (vl - 1)) 8 := rfl
  rw [h, h1]
  have := Nat.mul_le_mul_left (2 ^ (64 * (vl - 1))) htop
  omega

set_option maxHeartbeats 8000000 in
/-- **`Q.DivBasic.Pre` at the call** (`X`: the callee entry, `RSP = r - 400`; memory = the entry's up to the own frame;
`v`'s pointer / length stored at `r - 392` / `r - 384`) -/
theorem db_pre {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X : State} {ul' : Nat} (hpre : DrsPreW R b L H c W qp ql qc st up ul uc vp vl vc s) (hW : 4824 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hreg : X.mem.regions = s.mem.regions) (hle : ul' ≤ ul)
    (hU : natVal s.mem up ul' = natVal s.mem up ul) (hN : NatNorm s.mem up ul')
    (hvS : X.mem.readLE ((s.regs 4).toNat - 392) 8 = vp) (hlS : X.mem.readLE ((s.regs 4).toNat - 384) 8 = vl) :
    Q.DivBasic.Pre R b H L qp ql st up ul' uc vp vl X := by
  obtain ⟨hce, hsv, hgl, hqlc, hqc, hulc, huc, hvlc, hvc, hv2, ⟨hvl9, hql9⟩, htop, -, hU2,
    ⟨hqa, hq48, hqh, hqo, hqg⟩, ⟨hua, hu48, huh, huo, hug⟩, ⟨hva, hv48, hvh, hvo, -, -, -⟩, hqu, hqv, huv,
    hsti, ⟨hstl, hcap0, -⟩, ⟨hqs, hqf⟩, ⟨hus, huf⟩, ⟨hvs, hvf⟩, hswb, hsf, hfo, -, hcq, hinv, -, -, -,
    ⟨htq, htu, htst, htf⟩, -⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF.accessible a n w
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  obtain ⟨hok, hstw, hstg, harr⟩ := hsti
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hstw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hstw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hstw.of_sub (by omega) (by omega))
  have hlc := hok.2.2.2.2.2.1
  have hF1 : MemFrame s.mem X.mem (R.rt ++ win s W 96) := hF.mono fun a n ho => by
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho
    simp only [fw, win, outside_cons, outside_nil, and_true]; omega
  have hvt : 2 ^ 63 ≤ X.mem.readLE (vp + 8 * (vl - 1)) 8 := by
    rw [rdX _ _ (hvo.of_sub (by omega) (by omega))]; exact htop
  have hUX0 : X.mem.readLE up (8 * ul') = s.mem.readLE up (8 * ul') :=
    rdX _ _ (huo.of_sub (Nat.le_refl _) (by omega))
  have hUX : natVal X.mem up ul' = natVal s.mem up ul := hUX0.trans hU
  have hVX : natVal X.mem vp vl = natVal s.mem vp vl := rdX _ _ hvo
  have hroom := room_drsB (U := natVal s.mem up ul) (V := natVal s.mem vp vl) (ul := ul') (vl := vl) (ql := ql)
    (by omega) (v_geB (by omega) htop) hU2 (by
      rcases Nat.eq_zero_or_pos ul' with h0 | h0
      · exact Or.inl h0
      rcases hN with h | h
      · exact Or.inl h
      · right; rw [← hU]; exact natVal_ge _ _ _ h0 h)
  have hwin : ∀ a n, Outside a n (win s W 96) → Outside a n (win X 4424 88) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hwb := hgl.2.2.2.2.2.2.2.2.2.2.1
  have hst8 : X.mem.readLE ((X.regs 4).toNat + 8) 8 = vp := by rw [hsp, show (s.regs 4).toNat - 400 + 8 = (s.regs 4).toNat - 392 by omega]; exact hvS
  have hst16 : X.mem.readLE ((X.regs 4).toNat + 16) 8 = vl := by rw [hsp, show (s.regs 4).toNat - 400 + 16 = (s.regs 4).toNat - 384 by omega]; exact hlS
  unfold Q.DivBasic.Pre
  refine ⟨callEnv_shiftB hce hLs hF1 hsp h14 hfs hreg (by omega) (by omega) (by omega), hsv,
    by rw [hXacc]; exact hwb, hswb, hv2, hvt, by rw [hXacc]; exact hva, hv48, hvh, hwin _ _ hvo, by omega, by omega, huc,
    by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hua (Nat.le_refl _) (by omega), by omega,
    huh.sub (Nat.le_refl _) (by omega), hwin _ _ (huo.of_sub (Nat.le_refl _) (by omega)),
    by rw [h14]; unfold Apart at hug ⊢; omega, by omega, by rw [hXacc]; exact hqa, hq48, hqh, hwin _ _ hqo,
    by rw [h14]; exact hqg, by unfold Apart at hqu ⊢; omega, hqv, by unfold Apart at huv ⊢; omega,
    by rw [hUX, hVX]; exact hroom, stkOK_moveB hok eW eL eC hXacc, hwin _ _ hstw, by rw [h14]; exact hstg, ?starr,
    ?stgf, by rw [eL]; omega, by unfold Apart at hqs ⊢; omega, by unfold Apart at hus ⊢; omega,
    by unfold Apart at hvs ⊢; omega, ?free, by simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; exact hsf,
    by simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; exact hwin _ _ hfo,
    ⟨by rw [eL]; omega, by rw [stkR_congr eC]; omega⟩,
    by rw [h14]; exact RtInv.inv_frame' hF (fun r hr => by
      simp only [fw, win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; left; exact hout.of_sub (by simp only; omega) (by simp only; omega)) hinv,
    hst8, hst16, by rw [hfs]; exact htq, by rw [hfs]; unfold Apart at htu ⊢; omega, by rw [hfs]; exact htst,
    by simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; rw [hfs]; exact htf⟩
  case starr =>
    rw [eW, eC, h14]; intro hc; obtain ⟨h1, h2⟩ := harr hc; exact ⟨hwin _ _ h1, h2⟩
  case stgf =>
    simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]; rw [h14]
    obtain ⟨-, h2⟩ := harr hcap0
    unfold Apart at h2 ⊢; omega
  case free =>
    simp only [DivBasic.freeP, DivBasic.freeN, eW, eL, eC]
    refine ⟨?_, ?_, ?_⟩ <;> unfold Apart at hqf huf hvf ⊢ <;> omega

theorem qn_leB (ql ul vl : Nat) : DivBasic.qn ql ul vl ≤ ql := by
  simp only [DivBasic.qn]; split <;> omega

/-- the high part of a zero value is zero -/
theorem natVal_hi_zeroB {M : Memory} {p n k : Nat} (hk : k ≤ n) (h : natVal M p n = 0) :
    natVal M (p + 8 * k) (n - k) = 0 := by
  have e := natVal_add M p k (n - k)
  rw [show k + (n - k) = n by omega, h] at e
  have := Nat.two_pow_pos (64 * k)
  rcases Nat.eq_zero_or_pos (natVal M (p + 8 * k) (n - k)) with h0 | h0
  · exact h0
  · have := Nat.mul_le_mul (Nat.succ_le_of_lt this) (Nat.succ_le_of_lt h0); omega

/-- `U < V` when the normalised `len u` is below `len v` (= DrsPathC `u_lt_v`) -/
theorem u_lt_vB {M : Memory} {up ul ul' vp vl : Nat} (hv1 : 1 ≤ vl) (htop : 2 ^ 63 ≤ M.readLE (vp + 8 * (vl - 1)) 8)
    (hlt : ul' < vl) (hU : natVal M up ul' = natVal M up ul) : natVal M up ul < natVal M vp vl := by
  have h1 := natVal_lt M up ul'
  have h3 := natVal_ge M vp vl hv1 (by omega)
  have h4 : 2 ^ (64 * ul') ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- the frame step of `db_post` (small context) -/
theorem frameB {a n qp ql k up ul ul' st lo hi lo' hi' : Nat} {m : Memory} {rt : List (Nat × Nat)}
    (ho : Outside a n (rt ++ [(lo, hi)] ++ [(qp, qp + 8 * ql), (up, up + 8 * ul)] ++ stkWs m st))
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) (hk : k ≤ ql) (hu : ul' ≤ ul) :
    Outside a n (rt ++ [(lo', hi')] ++ [(qp, qp + 8 * k), (up, up + 8 * ul'), (st, st + 24),
      (stW m st + 8 * stLen m st, stW m st + 8 * stCap m st)]) := by
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := ho
  exact ⟨⟨h1, by omega⟩, by omega, by omega, h5, h6⟩

set_option maxHeartbeats 16000000 in
/-- **`Q.DivBasic.PostL` → `DrsPostW`** (pure; `s'` = the state after the epilogue, memory `T`'s) -/
theorem db_post {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X T s' : State} {ul' : Nat} (hpre : DrsPreW R b L H c W qp ql qc st up ul uc vp vl vc s) (hW : 4824 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14)
    (hle : ul' ≤ ul) (hU : natVal s.mem up ul' = natVal s.mem up ul)
    (hpost : Q.DivBasic.PostL R b H L qp ql st up ul' vp vl X T)
    (hm : s'.mem = T.mem) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) :
    DrsPostW R b L H c W qp ql st up ul vp vl s s' := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, hv2, -, htop, hq0, -,
    ⟨-, hq48, hqh, hqo, -⟩, ⟨-, hu48, huh, huo, -⟩, ⟨-, -, -, hvo, -, -, -⟩, hqu, -, -,
    hsti, -, ⟨hqs, hqf⟩, ⟨hus, huf⟩, -, -, -, -, -, hcq, -⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  obtain ⟨hok, hstw, -, -⟩ := hsti
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hstw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hstw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hstw.of_sub (by omega) (by omega))
  have hlc := hok.2.2.2.2.2.1
  obtain ⟨-, -, hqv, hrv, L', b', hx, hb, hinv, hSB, hMF, hLF⟩ := hpost
  simp only [DivBasic.ws, stkWs, eW, eL, eC] at hMF hLF
  rw [stkR_congr eC] at hb
  rw [h14] at hinv
  have hUX0 : X.mem.readLE up (8 * ul') = s.mem.readLE up (8 * ul') :=
    rdX _ _ (huo.of_sub (Nat.le_refl _) (by omega))
  have hUX : natVal X.mem up ul' = natVal s.mem up ul := hUX0.trans hU
  have hVX : natVal X.mem vp vl = natVal s.mem vp vl := rdX _ _ hvo
  rw [hUX, hVX] at hqv hrv
  have hqn := qn_leB ql ul' vl
  generalize hk : DivBasic.qn ql ul' vl = k at hqv hMF hLF hqn
  -- reads kept from `X` to `T`: held, outside the window, the written ranges
  have rdT : ∀ a n, Held R L a n → Outside a n (win s W 96) → a + n ≤ qp ∨ qp + 8 * k ≤ a →
      Apart a n up (8 * ul') → Apart a n st 24 →
      Apart a n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) →
      T.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh ho hq hu hs hf
    rw [FvModexp.Expmc.held_readLE (ws1 := win X 4424 88) hh hMF hLF ?_ ?_]
    · exact rdX a n ho
    · simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hsp]; omega
    · simp only [outside_cons, outside_nil, and_true]; unfold Apart at hu hs hf; omega
  have hqz : natVal s.mem qp ql = 0 := hq0
  unfold DrsPostW RtPostQ
  rw [hm, hfs, hdf]
  refine ⟨rfl, rfl, ?_, ?_, L', b', ⟨hx, by omega, hinv⟩, ?_, ?_, ?_⟩
  · -- `q`: `q[0:k]` = U/V, `q[k:]` kept (zero)
    have hhi : natVal T.mem (qp + 8 * k) (ql - k) = 0 := by
      rw [← natVal_hi_zeroB hqn hqz]; unfold natVal
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
      have := u_lt_vB (M := s.mem) (by omega) htop (by omega : ul' < vl) hU
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
  · obtain ⟨⟨hok', hlen, hor⟩, harr⟩ := hSB
    refine ⟨⟨hok', by rw [hlen, eL], ?_⟩, ?_⟩
    · rw [eW, eC] at hor; exact hor
    · intro hn; rw [← eW, ← eC] at hn; exact harr hn
  · refine hF.trans hMF fun a n ho => ⟨?_, ?_⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho
      simp only [fw, win, outside_cons, outside_nil, and_true]
      omega
    · simp only [win] at ho ⊢
      exact frameB ho (by rw [hsp]; omega) (by rw [hsp]; omega) hqn hle
  · refine ⟨fun a n hin ho => ?_⟩
    simp only [List.cons_append, outside_cons, List.nil_append, outside_nil, and_true] at ho
    rw [hLF.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; omega)]
    refine hF.readLE a n ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, outside_cons, outside_nil, and_true] at this ⊢
    omega

set_option maxHeartbeats 8000000 in
/-- the caller's slots above the callee window (`[r - 312, r + 96)`: saved `RBP`, return address) and accessibility
survive the `divBasic` call -/
theorem db_slot {R : RtInv} {b H : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X T : State} {ul' : Nat} (hpre : DrsPreW R b L H c W qp ql qc st up ul uc vp vl vc s) (hW : 4824 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (hle : ul' ≤ ul)
    (hpost : Q.DivBasic.PostL R b H L qp ql st up ul' vp vl X T) {a n : Nat} (h1 : (s.regs 4).toNat - 312 ≤ a)
    (h2 : a + n ≤ (s.regs 4).toNat + 96) :
    T.mem.readLE a n = X.mem.readLE a n ∧ ∀ a n w, T.mem.accessible a n w = s.mem.accessible a n w := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqo, -⟩, ⟨-, -, -, huo, -⟩, -, -, -, -,
    ⟨-, hstw, -, -⟩, -, -, -, -, -, -, hfo, -⟩ := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hce
  simp only [regSP] at hb' ha hw
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hstw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hstw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hstw.of_sub (by omega) (by omega))
  obtain ⟨-, -, -, -, L2, b2, -, -, -, -, hMF, -⟩ := hpost
  have hqn := qn_leB ql ul' vl
  simp only [DivBasic.ws, stkWs, eW, eL, eC] at hMF
  generalize DivBasic.qn ql ul' vl = k at hMF hqn
  simp only [win, outside_cons, outside_nil, and_true] at hqo huo hstw hfo
  refine ⟨hMF.readLE a n ?_, fun a n w => by rw [hMF.accessible, hF.accessible]⟩
  rw [outside_append, outside_append]
  refine ⟨⟨hout.of_sub (by omega) (by omega), ?_⟩, ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega

end FvModexp.Amd64.Q.DivRec
