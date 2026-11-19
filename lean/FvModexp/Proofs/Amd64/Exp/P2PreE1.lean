import FvModexp.Proofs.Amd64.Exp.P2Call
import FvModexp.Proofs.Amd64.Nat.DivmcCall
import FvModexp.Proofs.Common.StkFrame
import FvModexp.Proofs.Common.DivmcMem
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the call `buf = stk.nat((len + 1) w)` (nat.go:871) → the fill loop
head `FillJ 0` (agent divmc s62; twin of `Arm64/Exp/P2PreE1`)

* `snPre`: `stk.nat`'s Q-form precondition at its entry (`RSP_c = RSP - 184`, memory framed by the own window stores).
* `ctx0`: the context `Ctx` after `stk.nat`.
* `callSN`: `FillJ 0 → JN` — the call (return `+0xb1`) and the reloads `RDX = powers` (`RSP + 16`), `RSI = w`
  (`RSP - 48`), `RBX = len` (`RSP - 40`), `RDI = 0`, `JMP +0xd4`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

section
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

/-- the frame slots survive a frame whose written ranges miss `[RSP - 48, RSP + 80)` -/
theorem sl_frame {M M' : Memory} {rs : List (Nat × Nat)} (hsl : Sl s st pw pl lm x xl M) (hF : MemFrame M M' rs)
    (ho : ∀ a, (s.regs 4).toNat ≤ a + 48 → a + 8 ≤ (s.regs 4).toNat + 80 → Outside a 8 rs)
    (h48 : 48 ≤ (s.regs 4).toNat) : Sl s st pw pl lm x xl M' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hsl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a1
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a2
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a3
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a4
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a5
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a6
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a7
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a8
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a9
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a10
  · rw [hF.readLE _ _ (ho _ (by omega) (by omega))]; exact a11

set_option maxRecDepth 20000 in
/-- the stack header and the stack-object facts survive the function's own window stores -/
theorem stk_win (hpre : Pre R kc b L st pw pl ws lm x xl s) {M : Memory}
    (hF : MemFrame s.mem M (win s (K kc) A)) :
    StkOK M R L st ∧ stW M st = stW s.mem st ∧ stLen M st = stLen s.mem st ∧ stCap M st = stCap s.mem st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hok, hstw, -⟩, -⟩ := hpre
  exact stkOK_frame hok hF hstw (LiveExt.refl R L)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `stk.nat`'s Q-form precondition at its entry (`RSP_c = RSP - 184`) -/
theorem snPre {stkS aboveS : Nat} (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hpre : Pre R kc b L st pw pl ws lm x xl s) {S : State}
    (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 184)) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase) (hF : MemFrame s.mem S.mem (win s (K kc) A)) (hrg : S.mem.regions = s.mem.regions) :
    StackNatX.PreQ R (b + stkR (HP (stLen s.mem st) pl lm) s.mem st) L (HP (stLen s.mem st) pl lm) stkS aboveS st
      (NB pl lm) S := by
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hnb := nb_le hpl16 hw128
  obtain ⟨hok, e0, e1, e2⟩ := stk_win hpre hF
  obtain ⟨hce, hsv, hgl, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp0, hlen, -, -, hinv, -⟩ := hpre
  obtain ⟨-, -, hstw, -, harr, -, hfw, hsf, hswb, -⟩ := hsp0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, wacc, -⟩ := hgl
  have hce0 := hce
  obtain ⟨⟨-, -, -, -⟩, ⟨hb', -, -⟩, -, -, hout, -⟩ := hce0
  simp only [regSP, K] at hb'
  have hspN : (S.regs 4).toNat = (s.regs 4).toNat - 184 := by rw [hsp]; exact tN (by omega)
  simp only [StackNatX.PreQ]
  rw [e0, e1, e2]
  refine ⟨CallEnv.callee hce hspN h14 hfs (by decide) (by simp only [K]; omega) (by simp only [A]; omega) hF hrg,
    hsv, hok, ?_, fun hc0 => ?_, by omega, by omega, ⟨by simp only [HP, DPre, StackNat.rnd]; omega, ?_⟩, ?_,
    by rw [hF.accessible]; exact wacc, hswb, hsf⟩
  · simp only [win, K, A, outside_cons, outside_nil, and_true] at hstw ⊢; rw [hspN]; omega
  · obtain ⟨o1, o2⟩ := harr hc0
    refine ⟨?_, by rw [h14]; exact o2⟩
    simp only [win, K, A, outside_cons, outside_nil, and_true] at o1 ⊢
    rw [hspN]; omega
  · rw [stkR_congr e2]; omega
  · rw [h14]
    refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) hinv
    simp only [win, List.mem_singleton] at hr
    subst hr; dsimp only
    rw [show (s.regs 4).toNat + A - ((s.regs 4).toNat - K kc) = K kc + A by simp only [K]; omega]
    exact hout

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the context after `stk.nat`** (`S` the callee entry state, `s'` its return state) -/
theorem ctx0 (hpre : Pre R kc b L st pw pl ws lm x xl s) {S s' : State}
    (hF : MemFrame s.mem S.mem (win s (K kc) A)) (hrg : S.mem.regions = s.mem.regions)
    (hsl : Sl s st pw pl lm x xl S.mem)
    (hspN : (S.regs 4).toNat = (s.regs 4).toNat - 184) {stk above : Nat} (hk : stk ≤ kc)
    (ha : above ≤ 88) (hrg' : s'.mem.regions = S.mem.regions)
    {L' : List (Nat × Nat)} {b' : Nat} (hLE : LiveExt R L L')
    (hinv : R.inv (b' + stkR (HP (stLen s.mem st) pl lm) s'.mem st) L' (s.regs 14).toNat (view R.rt L' s'.mem))
    (hok : StkOK s'.mem R L' st) (hlen : stLen s'.mem st = stLen S.mem st + StackNat.rnd (NB pl lm))
    (hsame : stLen S.mem st + StackNat.rnd (NB pl lm) ≤ stCap S.mem st →
      stW s'.mem st = stW S.mem st ∧ stCap s'.mem st = stCap S.mem st)
    (hgrow : stCap S.mem st < stLen S.mem st + StackNat.rnd (NB pl lm) →
      InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧ ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L)
    (hF' : MemFrame S.mem s'.mem (R.rt ++ win S stk above ++ stkWs S.mem st))
    (hLF' : LiveFrame S.mem s'.mem L (stkWs S.mem st))
    (hmemb : stCap S.mem st < stLen S.mem st + StackNat.rnd (NB pl lm) →
      (stW s'.mem st, stW s'.mem st + 8 * stCap s'.mem st) ∈ L') :
    Ctx R kc L st pw pl lm x xl s (stW s'.mem st + 8 * stLen s.mem st) s'.mem L' b' := by
  obtain ⟨-, e0, e1, e2⟩ := stk_win hpre hF
  simp only [e0, e1, e2] at hsame hgrow hlen hmemb
  have hnb : 0 < NB pl lm := Nat.mul_pos (by have := (pl_facts hpre).1; omega) (w_facts hpre).1
  have hws : stkWs S.mem st = stkWs s.mem st := by simp only [stkWs]; rw [e0, e1, e2]
  rw [hws] at hF' hLF'
  obtain ⟨hce, -, hgl, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp0, -⟩ := hpre
  obtain ⟨-, ⟨-, hsth, -, -, -, hlc, -⟩, hstw, -, harr, -, hfw, hsf, -, -, hsgA, hfgA, -⟩ := hsp0
  obtain ⟨-, -, -, -, -, -, -, -, grt, -⟩ := hgl
  obtain ⟨⟨-, -, -, -⟩, ⟨hb', hA', -⟩, -, -, hout, -, -, hLs, -⟩ := hce
  simp only [regSP, K, A] at hb' hA' hout
  simp only [win, K, A, Q.BasicSqr.freeP, Q.BasicSqr.freeN, outside_cons, outside_nil, and_true] at hstw hfw
  -- the frame
  have hfr : MemFrame s.mem s'.mem (AW R kc s pw pl st) := by
    refine hF.trans hF' fun a n h => ?_
    simp only [AW, LW, outside_append] at h
    obtain ⟨⟨h1, h2⟩, -, h4⟩ := h
    refine ⟨h2, ?_⟩
    simp only [outside_append]
    refine ⟨⟨h1, ?_⟩, h4⟩
    simp only [win, K, A, outside_cons, outside_nil, and_true] at h2 ⊢
    rw [hspN]; omega
  have hlf : LiveFrame s.mem s'.mem L (LW s pw pl st) := by
    refine LiveFrame.trans (L' := L) ?_ (LiveFrame.mono_ws hLF' fun a n h => ?_) fun a n h => h
    · refine Expmc.liveFrame_of_frame hF fun a n hin _ => ?_
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := hLs r hr
      simp only [win, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [LW, outside_append] at h; exact h.2
  -- the scratch nat
  have hscr : Scr R L L' s.mem s'.mem st (stW s'.mem st + 8 * stLen s.mem st) (NB pl lm) :=
    Scr.of_post hok hlen hnb hsame hgrow rfl
  have hsa : StkAfter R L L' st (stLen s.mem st) pl lm s.mem s'.mem := by
    refine ⟨hok, hlen, ?_⟩
    by_cases hc : stLen s.mem st + StackNat.rnd (NB pl lm) ≤ stCap s.mem st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  have hsap : StkSep s'.mem st (stW s'.mem st + 8 * stLen s.mem st) (8 * NB pl lm) := by
    simp only [StkSep, Q.BasicSqr.freeP, Q.BasicSqr.freeN]
    refine ⟨?_, by rw [hlen]; unfold Apart; simp only [StackNat.rnd]; omega, ?_⟩
    · rcases hscr.loc with ⟨h0, l1, l2⟩ | ⟨hin, hap⟩
      · have := hsf; simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at this; unfold Apart at this ⊢; omega
      · rcases hsth with hL | hO
        · have := hap.apart_of_inRanges hL; unfold Apart at this ⊢; omega
        · have := hin.apart hO; unfold Apart at this ⊢; omega
    · rcases hscr.loc with ⟨h0, l1, l2⟩ | ⟨hin, -⟩
      · have := hfgA; simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at this; unfold Apart at this ⊢; omega
      · have := hin.apart grt; unfold Apart at this ⊢; omega
  have hain : ArrIn L' st s.mem s'.mem := ArrIn.of_nat hok.2.2.2.2.2.1 hlen hsame hmemb
  have hbu : BU s'.mem st (stW s'.mem st + 8 * stLen s.mem st) (8 * NB pl lm) := by
    left; rw [hlen]; simp only [StackNat.rnd]; omega
  refine ⟨hfr, hlf, hrg'.trans hrg, hLE, hinv, hscr, hsa, hsap, ?_, hain, hbu⟩
  refine sl_frame hsl hF' (fun a h1 h2 => ?_) (by omega)
  simp only [stkWs, win, outside_append, outside_cons, outside_nil, and_true]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by rw [hspN]; omega⟩, by omega, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`buf = stk.nat((len+1) w)`** from the callee entry, then the reloads → `FillJ 0` -/
theorem callSN {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsn : StackNatX.HypQ impl R ns stkS aboveS) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (kF : FillJ impl R kc b L st pw pl ws lm x xl s 0) : JN impl R kc b L st pw pl ws lm x xl s := by
  intro S hpre hpc ⟨hsp, h5, h14, hfs, hx15, hdf⟩ hrd h0 h3 hF hrg hsl
  have hK : 184 + kc ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simpa only [regSP, K] using this
  have hR64 := (s.regs 4).isLt
  have hspN : (S.regs 4).toNat = (s.regs 4).toNat - 184 := by rw [hsp]; exact tN (by omega)
  obtain ⟨hok, e0, e1, e2⟩ := stk_win hpre hF
  have hnb0 : 0 < NB pl lm := nb_pos (by have := (pl_facts hpre).1; omega) (w_facts hpre).1
  have hnb := nb_le (pl_facts hpre).2.1 (w_facts hpre).2
  have hst64 : st < 2 ^ 64 := by have := hok.2.2.2.1; omega
  have hx15s : s.xmm 15 = 0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdfs : s.df = false := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  unfold Goal
  refine stkNatCallQ hap hns hsn (HP (stLen s.mem st) pl lm) (b := b + stkR (HP (stLen s.mem st) pl lm) s.mem st)
    (L := L) (ra_bp hap hnf 0xb1 (by decide)) hpc (by rw [hspN]; exact hrd) h0 h3 (by rw [hx15, hx15s])
    (by rw [hdf, hdfs]) hst64 (by omega) (snPre hkS haS hpre hsp h14 hfs hF hrg)
    fun s' hpc' hsp' h5' h14' hx15' hrg' hpost => ?_
  obtain ⟨efs, edf, hr0, -, hr1, L', b', ⟨hLE, hbud, hinv'⟩, hok', hlen, hsame, hgrow, hF', hLF', hmemb⟩ := hpost
  rw [stkR_congr e2] at hbud
  have hle : stkR (HP (stLen s.mem st) pl lm) s'.mem st ≤ b' := by omega
  have hinv2 : R.inv (b' - stkR (HP (stLen s.mem st) pl lm) s'.mem st + stkR (HP (stLen s.mem st) pl lm) s'.mem st) L'
      (s.regs 14).toNat (view R.rt L' s'.mem) := by
    rw [Nat.sub_add_cancel hle, ← h14]; exact hinv'
  have hbud2 : b ≤ b' - stkR (HP (stLen s.mem st) pl lm) s'.mem st := by omega
  generalize b' - stkR (HP (stLen s.mem st) pl lm) s'.mem st = b2 at hinv2 hbud2
  clear hbud hle
  have hc := ctx0 hpre hF hrg hsl hspN hkS haS hrg' hLE hinv2 hok' hlen hsame hgrow hF' hLF' hmemb
  rw [e1] at hr0
  have hr0' := hr0 hnb0
  obtain ⟨-, -, -, f3, -, -, -, -, -, f10, f11⟩ := hc.sl
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simp only [K, regSP] at this; omega
  have hR64 := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := by have := hpre.1.2.1.2.1; simpa only [regSP, A] using this
  have hwm : s'.mem.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    rw [hsp', hsp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have g1 : s'.mem.readLE ((s.regs 4).toNat - 176 + 192) 8 = pw := by
    rw [show (s.regs 4).toNat - 176 + 192 = (s.regs 4).toNat + 16 by omega]; exact f3
  have g2 : s'.mem.readLE ((s.regs 4).toNat - 176 + 128) 8 = W lm := by
    rw [show (s.regs 4).toNat - 176 + 128 = (s.regs 4).toNat - 48 by omega]; exact f11
  have g3 : s'.mem.readLE ((s.regs 4).toNat - 176 + 136) 8 = pl := by
    rw [show (s.regs 4).toNat - 176 + 136 = (s.regs 4).toNat - 40 by omega]; exact f10
  have h5'' := h5'.trans h5
  have h14'' := h14'.trans h14
  have hx15'' := hx15'.trans hx15
  have edf' := edf.trans hdf
  have hpreH : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  have hcH : Hide (Ctx R kc L st pw pl lm x xl s (stW s'.mem st + 8 * stLen s.mem st) s'.mem L' b2) := ⟨hc⟩
  clear hF' hLF' hF hsame hgrow hpre hc hok hok' hsl hLE hinv' hinv2 e0 e2 hlen hr0 hmemb
  have hpc2 : s'.rip = BitVec.ofNat 64 snR := hpc'
  clear hpc' hsp'
  janus64_run [g1, g2, g3, hwm] until [pcF]
  refine kF _ _ L' b2 hpreH.h rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ hcH.h
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (Nat.zero_le _) hbud2
  all_goals first | exact efs.trans hfs | janus64_simp

end

end FvModexp.Amd64.P2Pre
