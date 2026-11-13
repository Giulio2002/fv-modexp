import FvModexp.Proofs.Amd64.NatQ.DrsSNP
import FvModexp.Proofs.Amd64.Nat.StackNatX
import FvModexp.Proofs.Amd64.Nat.Callees2

set_option autoImplicit false

/-! (amd64 twin of Arm64/NatQ/DrsNat.lean + the `snSum` / `raS` of Arm64/NatQ/DrsSN.lean, asm s45)
# `divRecursiveStep` (amd64): `qhat0 := stk.nat(B + 1)` (`CALL 0x5ef9d8`, return `0x5ef9dd`) — the callee

`snSum`: `StackNatX.ensQ` (window `4192 / 24`) as a summary on `LibDrs`; `raS`: the return site `0x5ef9dd` is admissible
for `(*stack).nat`'s program; `sn_pre`: `StackNatX.PreQ … 4192 24 st (B + 1)` at the callee entry (`RSP = r - 400`,
memory = the entry's up to the own frame `fw s`). The retAddr helpers and `callEnv_shiftN` are local copies of
DrsPathB's (so that the big path does not import the `divBasic` modules).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem drsN_pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
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
      · exact drsN_pairwise_ne hR hp.2 ha' hb' hne

theorem drsN_find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact drsN_find_none_of h x hx'

theorem drsN_retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
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
    have := drsN_pairwise_ne (fun a b h => by unfold Amd64.Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Amd64.Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Amd64.Program.stubAt at h1
    have := drsN_find_none_of h1 st hst
    simp at this
    exact this

set_option maxRecDepth 20000 in
/-- the return site `0x5ef9dd` (after `CALL (*stack).nat`) is admissible for `(*stack).nat`'s program -/
theorem raS (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) 0x5ef9dd := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := StackNat.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by decide) 0x15d (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option linter.defProp false in
/-- `(*stack).nat`'s `ensQ` (window `4192 / 24`) as a summary in `LibDrs.program.link impl` -/
def snSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) :=
  FvModexp.Amd64.Callees.Ensures.toSummaryRegs2 (fun a0 a1 => StackNatX.ensQ impl hap R hgr hmc hwb H b L a0 a1)
    (A64.noExit_restrict64 hap StackNat.names)
    (show CodeIn64 ((Extracted.program.onlySegments StackNat.names).link impl) (LibDrs.program.link impl) by
      rw [LibDrs.eq_only]; exact A64.codeIn_restrict_mono64 hap (FvModexp.Amd64.Callees.sub_of_all (by decide)))

theorem callEnv_shiftN {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
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

set_option maxHeartbeats 8000000 in
/-- **`StackNatX.PreQ` at `stk.nat(B + 1)`** (callee entry `X`, `RSP = r - 400`) -/
theorem sn_pre {R : RtInv} {b Hq : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X : State} (hpre : DrsPreW R b L Hq c W qp ql qc st up ul uc vp vl vc s) (hW : 4992 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hreg : X.mem.regions = s.mem.regions) (hv9 : vl ≤ 2 ^ 9) :
    StackNatX.PreQ R b L Hq 4192 24 st (vl / 2 + 1) X := by
  have hce := hpre.ce
  have hce' := hce
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hb'
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF.accessible a n w
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [win, fw, outside_cons, outside_nil, and_true] at h ⊢; omega)
  obtain ⟨hok, hstw, hstg, harr⟩ := hpre.sti
  have hsw : Outside st 24 (win s W 96) := hstw
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hsw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have hF1 : MemFrame s.mem X.mem (R.rt ++ win s W 96) := hF.mono fun a n ho => by
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho
    simp only [fw, win, outside_cons, outside_nil, and_true]; omega
  have hwin : ∀ a n, Outside a n (win s W 96) → Outside a n (win X 4192 24) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hstl := hpre.stl.1
  have hcb := hpre.cost
  refine ⟨callEnv_shiftN hce hLs hF1 hsp h14 hfs hreg (by omega) (by omega) (by omega), hpre.sv,
    stkOK_moveR hok eW eL eC hXacc, hwin _ _ hsw, ?arr, by omega, by rw [eL]; omega,
    ⟨by rw [eL]; omega, by rw [stkR_congr eC]; omega⟩,
    by rw [h14]; exact RtInv.inv_frame' hF (fun r hr => by
      simp only [fw, win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; left; exact hout.of_sub (by simp only; omega) (by simp only; omega)) hpre.inv,
    by rw [hXacc]; exact hpre.gl.2.2.2.2.2.2.2.2.2.2.1, hpre.wbap, by rw [eW, eL, eC]; exact hpre.hf⟩
  case arr => rw [eW, eC, h14]; intro hc; obtain ⟨h1, h2⟩ := harr hc; exact ⟨hwin _ _ h1, h2⟩

end FvModexp.Amd64.Q.DivRec
