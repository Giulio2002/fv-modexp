import FvModexp.Proofs.Amd64.Exp.P2PreBld
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `runtime.memmove(dst, src, 8)` into `buf` (agent divmc s63; twin of
infra's `Arm64/Exp/P2PreMv`)

`mvCall`: at the live `memmove` contract (`RSP_c = RSP - 184`, the return address pushed) with `dst = [d, d + 8)` inside
`buf` and a readable source outside the callee's window: the continuation gets the return state with the context, the
kept reads (`powers`, `buf` apart from `dst`, the frame above the callee's argument area) and the copied word.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

/-- `runtime.memmove`'s contract address -/
abbrev mvE : Nat := 4763104

theorem mvE_eq : cA "runtime.memmove" = mvE := by decide

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`memmove(d, src, 8)`** called at `S` (`RSP_c = RSP - 184`, return address at `[RSP_c]`, context at `S.mem`) -/
theorem mvCall (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {r : W64} {Q : State → Prop}
    {S : State} (hpc : S.rip = BitVec.ofNat 64 mvE) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 184)
    (h14 : S.regs 14 = s.regs 14) (hm : S.mem = M) (hra : M.readLE ((s.regs 4).toNat - 184) 8 < 2 ^ 47)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false) {d src : Nat} (h0 : S.regs 0 = BitVec.ofNat 64 d)
    (h3 : S.regs 3 = BitVec.ofNat 64 src) (h1 : S.regs 1 = BitVec.ofNat 64 8)
    (hd1 : bp ≤ d) (hd2 : d + 8 ≤ bp + 8 * NB pl lm)
    (hsa : M.accessible src 8 false = true) (hs48 : src + 8 ≤ 2 ^ 48)
    (hsw : src + 8 ≤ (s.regs 4).toNat - 184 - 4096 ∨ (s.regs 4).toNat - 184 + 32 ≤ src)
    (k : ∀ (junk : Nat → W64) (f : Flags) (xm yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256)
      (kr : Nat → W64), Ctx R kc L st pw pl lm x xl s bp m L1 b1 →
      (∀ a n, 0 < n → ((pw ≤ a ∧ a + n ≤ pw + 24 * pl) ∨ (bp ≤ a ∧ a + n ≤ bp + 8 * NB pl lm) ∨
        ((s.regs 4).toNat - 152 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 80)) → (a + n ≤ d ∨ d + 8 ≤ a) →
        m.readLE a n = M.readLE a n) →
      m.readLE d 8 = M.readLE src 8 →
      ReachesRet (LibW.program.link impl) r (retState64 S junk [] f xm yh m zh kr) Q) :
    ReachesRet (LibW.program.link impl) r S Q := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  simp only [K] at hK
  have hR64 := (s.regs 4).isLt
  have hce := cenv_ctx hpre hc
  obtain ⟨hal, hb', ha8, hw, hg24, hgacc, hgk, hout, hga, -, hLs, -⟩ := hce
  have hsv := hpre.2.1
  have hok : R.ok mvE [d, src, 8] := by rw [← mvE_eq]; exact hsv.2.1 d src 8 (by decide)
  have hwok := wok_buf (zp := d) (zn := 8) hc.scr hd1 hd2
  have hwin := wok_win hwok hf.w (by simp only; omega)
  simp only [K, A] at hwin
  have hdh : Held R L1 d 8 := hc.scr.held.sub hd1 hd2
  have hdacc : M.accessible d 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hc.scr.acc hd1 (by omega)
  have hd48 : d + 8 ≤ 2 ^ 48 := by have := hc.scr.b48; omega
  have t0 : (BitVec.ofNat 64 d).toNat = d := tN (by omega)
  have t3 : (BitVec.ofNat 64 src).toNat = src := tN (by omega)
  have t1 : (BitVec.ofNat 64 8 : BitVec 64).toNat = 8 := rfl
  have e0 : (S.regs 0).toNat = d := by rw [h0]; exact t0
  have e3 : (S.regs 3).toNat = src := by rw [h3]; exact t3
  have e1 : (S.regs 1).toNat = 8 := by rw [h1]; rfl
  unfold Apart at hga
  refine ReachesRet.call_regions (hmv L1 (b1 + stkR (HP (stLen s.mem st) pl lm) M st)) hpc ?_ ?_
  · simp only [MemPre64, MemAmd64.EqPre, MemAmd64.CallOK, LiveMemAt64, liveWin64,
      MemAmd64.Input, LiveDest64, MapAmd64.calleeStack, calleeStack64, hsp, e0, e1, e3, h14, hm, hx15, hdf,
      List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨?_, ⟨by omega, by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega),
      trivial, trivial, hra⟩, by omega⟩, ⟨hok, hc.inv, ?_, ?_⟩, ⟨hs48, hsa, by omega⟩,
      ⟨hd48, hdacc, by omega, hdh, by omega⟩⟩
    · exact ⟨by simp only [regG, stackguard0Offset, h14]; omega, by simp only [regG, stackguard0Offset, h14, hm]; exact hgacc,
        by simp only [stackguard0, regG, regSP, stackguard0Offset, h14, hm, hsp]; omega⟩
    · intro r' hr'
      have := hLs r' hr'
      simp only [outside_cons, outside_nil, and_true] at this ⊢
      omega
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact hout.of_sub (by omega) (by simp only; omega)
      · exact hout.of_sub (by simp only; omega) (by simp only; omega)
      · exact hout.of_sub (by simp only; omega) (by simp only; omega)
  intro S2 _ ⟨junk, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hinv2, hcp⟩ hrg0
  subst hs2
  simp only [e0, e1, e3, hm, calleeStack64, hsp, h14] at hfr2 hlf2 hinv2 hcp
  have hrg : m'.regions = M.regions := by rw [← hm]; exact hrg0
  have hws : ∀ r' ∈ [(d, d + 8)], WOK R L s st r' := by
    intro r' hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hwok
  have hF' : MemFrame M m' (R.rt ++ win S 4096 32 ++ [(d, d + 8)]) := hfr2.mono fun a n ho => by
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    rw [hsp] at ho; exact ⟨⟨ho.1.1, by omega, by omega⟩, ho.2⟩
  have hhdr : ∀ c n, st ≤ c → c + n ≤ st + 24 → m'.readLE c n = M.readLE c n := fun c n e1 e2 => by
    have hd := hf.w.hd
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hd
    have hz := hc.sa.1.2.1
    refine rd_keep hf.w hsp (by omega) (by omega) hF' hlf2 (hz.sub e1 e2) (by simp only [K, A]; omega)
      fun r hr hr' => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only at hr' ⊢
    have hs1 := hc.sap.1
    unfold Apart at hs1
    omega
  have hsah := sa_hdr' hc.ain hc.bu hc.sa hc.sap (LiveExt.refl R L1) hhdr hF'.accessible
  have hcap : stCap m' st = stCap M st := hhdr _ _ (by omega) (by omega)
  have hc2 := keepC hc hf.w hsp (by omega) (by omega) hws hF' hlf2 hrg (LiveExt.refl R L1)
    (by rw [stkR_congr hcap]; exact hinv2) hsah.1 hsah.2.1 hsah.2.2.1 hsah.2.2.2
  refine k junk f2 x2 yh2 m' zh2 kr2 hc2 (fun a n h0' hr hd => ?_) ?_
  · have hws' : ∀ r ∈ [(d, d + 8)], r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a := fun r hr _ => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd
    rcases hr with hr | hr | hr
    · have hpww := hf.pww
      simp only [win, K, A, outside_cons, outside_nil, and_true] at hpww
      exact rd_keep hf.w hsp (by omega) (by omega) hF' hlf2 (Or.inr (hf.pwrt.of_sub hr.1 hr.2))
        (by simp only [K, A]; omega) hws'
    · have hw2 := wok_win (wok_buf (zp := a) (zn := n) hc.scr hr.1 hr.2) hf.w (by simp only; omega)
      exact rd_keep hf.w hsp (by omega) (by omega) hF' hlf2 (hc.scr.held.sub hr.1 hr.2) hw2 hws'
    · refine frame_read hF' fun r' hr' hr'' => ?_
      simp only [List.mem_append, win, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with (hr' | hr') | hr'
      · have hrt := hf.w.rt
        simp only [K, A] at hrt
        have := MemFrame.outside_mem (hrt.of_sub (a := a) (n := n) (by omega) (by omega)) hr'; omega
      · subst hr'; simp only at hr'' ⊢; rw [hsp]; omega
      · subst hr'; simp only at hr'' ⊢; omega
  · exact Expmc.readLE_of_copied hcp

end

end FvModexp.Amd64.P2Pre
