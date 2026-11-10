import FvModexp.Proofs.Arm64.Top.RunRel

/-! # `Run` (arm64): entry to the first boundary `B1` (prologue, header 0 = `baseLen`: `getData`, std `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem h1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (hs : CallSetup ((LibRun.program.link impl).withExit ret) (segAddr Extracted.program fn) [c, p, len, cp] s)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) (hokr : HdrOkR R b len)
    (Q : Outcome → Prop)
    (hk : ∀ S L1 b1, RelH R b L c p len cp s ret 1 L1 b1 S → S.pc = BitVec.ofNat 64 pcB1 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q) :
    Reaches ((LibRun.program.link impl).withExit ret) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hok, hcost, hokm⟩ := hokr
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hmvD := MemmoveLive.withData hmv' hro
  have hap1 := hap.1
  have hLs0 := hLs
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw
  janus_intro hs
  simp only [LiveSep, win] at hLs
  simp only [win, Outside, and_true] at hpw hcw
  unfold Apart at hga
  janus_data hd
  have hS := RunCallees.sbStdD impl hap R hmk b L
  have hwS : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwS hok
  have hLS1 : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; omega
  have hBuf : InRanges (BitVec.toNat s.sp - 296) 32 L ∨ Outside (BitVec.toNat s.sp - 296) 32 R.rt :=
    Or.inr (hout.of_sub (by omega) (by omega))
  by_cases h32 : len.toNat < 32
  · have hmvok : R.ok (cA "runtime.memmove") [s.sp.toNat - 296, p.toNat, len.toNat] := hokm (by omega) _ _ _ (by omega)
    have hc : (len.toNat < 32) = True := by simp; omega
    clear hokm
    set_option janus.callRegions true in
    janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc] until [segAddr Extracted.program fn + 0x8c] calls [hmv']
    rename_i _ _ _ m _ _ hMF hLF hinv1 hcp
    rw [List.append_assoc] at hMF
    have hd1 := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMF ?w ?ws
    case d0 => janus_callpre
    case w => simpa only [Memory.accessible_writeLE] using hw
    case ws =>
      intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    clear hd
    janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc] until [pcB1] calls [hS]
    refine hk _ ?L1 ?b1 ?rel (by janus_simp)
    case rel =>
    unfold RelH
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (janus_simp; done)
    all_goals try (with_reducible assumption)
    all_goals trace_state
    all_goals sorry
  · have hH0 : InRanges p.toNat 32 L ∨ Outside p.toNat 32 R.rt := hheld.sub (Nat.le_refl _) (by omega)
    have hW0 : p.toNat + 32 ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ p.toNat := by omega
    have hc : (len.toNat < 32) = False := by simp; omega
    clear hokm
    janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc] until [pcB1] calls [hS]
    all_goals trace_state
    all_goals sorry

end FvModexp.Arm64.Run
