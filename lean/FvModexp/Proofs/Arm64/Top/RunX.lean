import FvModexp.Proofs.Arm64.Top.RunDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcL : Nat := segAddr Extracted.program fn + 0x25c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem x (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (LibRun.program.link impl) (segAddr Extracted.program fn) [c, p, len, cp]
      (fun s => CallEnv R L s 4800 40 ∧ 96 ≤ len.toNat ∧ p.toNat + len.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible p.toNat len.toNat false = true ∧ Held R L p.toNat len.toNat ∧
        Outside p.toNat len.toNat (win s 4800 40) ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        R.ok (cA "runtime.makeslice") [SetBytesStd.wordT, 4, makeCap 4] ∧ 3 * makeCost 4 ≤ b ∧
        (∀ d sr n, n ≤ 32 → R.ok (cA "runtime.memmove") [d, sr, n]))
      (fun _ _ => True) := by
  intro ret hret s hs ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hlen, hp, hpacc, hheld,
    hpw, hinv, hok, hcost, hokm⟩
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hmvD := MemmoveLive.withData hmv' hro
  have hap1 := hap.1
  janus_intro hs
  simp only [LiveSep, win] at hLs
  simp only [Outside, and_true] at hpw
  unfold Apart at hga
  janus_data hd
  have hS := RunCallees.sbStdD impl hap R hmk
  have hwS : Outside SetBytesStd.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytesStd.wordT
  rw [h_t] at hwS hok
  have hLS1 : ∀ r ∈ L, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; omega
  have hH : ∀ o, o + 32 ≤ len.toNat → InRanges (p.toNat + o) 32 L ∨ Outside (p.toNat + o) 32 R.rt :=
    fun o ho => (hheld.sub (a := p.toNat + o) (n := 32) (by omega) (by omega))
  have hH0 := hH 0 (by omega); have hH1 := hH 32 (by omega); have hH2 := hH 64 (by omega)
  simp only [Nat.add_zero] at hH0
  have hW : ∀ o, o + 32 ≤ len.toNat → p.toNat + o + 32 ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ p.toNat + o := by
    intro o ho; omega
  have hW0 := hW 0 (by omega); have hW1 := hW 32 (by omega); have hW2 := hW 64 (by omega)
  simp only [Nat.add_zero] at hW0
  have hc32 : (len.toNat < 32) = False := by simp; omega
  have hc64 : (len.toNat < 64) = False := by simp; omega
  have hc96 : (len.toNat < 96) = False := by simp; omega
  janus_run [natLive_zero, toInt_ite, toNat_ite, toInt_small, hc32, hc64, hc96] until [pcL] calls [hS, hmvD]
  all_goals trace_state
  all_goals sorry

end FvModexp.Arm64.Run
