import FvModexp.Proofs.Amd64.Exp.W4Posts
import FvModexp.Proofs.Amd64.Exp.W4Seg
import FvModexp.Proofs.Amd64.Exp.W4ExA
import FvModexp.Proofs.Amd64.Exp.CmpW

set_option autoImplicit false

/-!
# window-4 (amd64), the first `zz.cmp(m)` (nat.go:1485) and its two branches (agent expmc s46)

Twin of `Arm64.W4Loop.exLt`/`exGe` (+ the cmp call of `exB`). From `nat.cmp`'s entry (`W4Loop.exA`'s continuation
state): the call (asm's `CmpSum.cmp_summary`, frame inside the loop's callee window, so `Mem` is kept), then
* `cmp < 0` (`zz < m`): `zz` reloaded into `DI, SI, R8` → the join `+0x11f3` (the inline `zz.norm()` loop test);
* `cmp ≥ 0` (`m ≤ zz`): the arguments of `zz.sub(zz, m)` and the `CALL` (return `+0x1130`) → `nat.sub`'s entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Loop

abbrev subE : Nat := 6183136

theorem cmpCodeIn (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.CmpAmd64.program (LibW.program.link impl) := by
  rw [LibW.eq_only]
  exact Callees.codeIn_single hap (seg := Extracted.seg15) rfl
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide)

theorem cmpSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibW.program.link impl) 6184128 CmpSum.Pre CmpSum.Post :=
  Summary.of_codeIn64 (cmpCodeIn impl hap) CmpSum.cmp_summary

theorem outside_of_win {ws : List (Nat × Nat)} {lo hi a k : Nat} (hws : ∀ r ∈ ws, lo ≤ r.1 ∧ r.2 ≤ hi)
    (h : Outside a k [(lo, hi)]) : Outside a k ws := by
  induction ws with
  | nil => trivial
  | cons r ws ih =>
    have h1 := hws r (List.mem_cons_self ..)
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨by omega, ih (fun r' hr' => hws r' (List.mem_cons_of_mem _ hr'))⟩

/-- a frame inside the loop's callee window `[sp - 4296, sp + 0x60)` (regions unchanged) keeps `Mem` -/
theorem Mem.frameW {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g fs sp : Nat} {M0 M M' : Memory}
    {zp zc zzp zzc : Nat} (h : Mem R b L g sp M0 M zp zc zzp zzc) (he : Env R L g fs sp M0) {ws : List (Nat × Nat)}
    (hf : MemFrame M M' ws) (hws : ∀ r ∈ ws, sp - 4296 ≤ r.1 ∧ r.2 ≤ sp + 0x60 ∧ r.1 ≤ r.2)
    (hrg : M'.regions = M.regions) : Mem R b L g sp M0 M' zp zc zzp zzc := by
  have hLs := he.2.2.2.2.2.2.2.2.2.2.1
  have hrt := he.2.2.2.2.2.2.2.1
  have hs : 4296 ≤ sp := he.2.1
  refine ⟨⟨h.1.1.trans hf (fun a k ho => ⟨ho, outside_of_win (fun r hr => ⟨(hws r hr).1, (hws r hr).2.1⟩) ?_⟩),
    h.1.2.trans (FvModexp.Expmc.liveFrame_of_frame hf (fun a k hin _ => outside_of_win (fun r hr => ⟨(hws r hr).1, (hws r hr).2.1⟩) ?_)) (fun _ _ h => h)⟩,
    FvModexp.Expmc.inv_frame hf ?_ h.2.1, by rw [hrg]; exact h.2.2⟩
  · simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  · intro r hr
    have := hws r hr
    exact Or.inr (hrt.of_sub (by omega) (by omega))

theorem cmp_lt {n X Y : Nat} (h : X < Y) : CmpSum.cmpRes n n X Y = 18446744073709551615#64 := by
  simp [CmpSum.cmpRes, h]

theorem cmp_ge {n X Y : Nat} (h : ¬ X < Y) : (CmpSum.cmpRes n n X Y).msb = false := by
  unfold CmpSum.cmpRes; simp only [Nat.lt_irrefl, ↓reduceIte, h]; split <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the first `zz.cmp(m)` and its two branches -/
theorem exCmp {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) {ret : W64} {Q : State → Prop}
    (S : State) (r5 : W64) (zp zc zzp zzc : Nat)
    (hpc : S.rip = BitVec.ofNat 64 cmpE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hra : S.mem.readLE (sp - 8) 8 = fnE + 0x10d0) (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h7 : S.regs 7 = BitVec.ofNat 64 mp) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (r188 : S.mem.readLE (sp + 0x188) 8 = zzp) (r98 : S.mem.readLE (sp + 0x98) 8 = n)
    (ra0 : S.mem.readLE (sp + 0xa0) 8 = zzc)
    (KLt : ∀ S' : State, S'.rip = BitVec.ofNat 64 njoin → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 zzp → S'.regs 6 = BitVec.ofNat 64 n → S'.regs 8 = BitVec.ofNat 64 zzc →
      Mem R b L g sp M0 S'.mem zp zc zzp zzc → S'.mem.readLE zzp (8 * n) = S.mem.readLE zzp (8 * n) →
      MemFrame S.mem S'.mem [(sp - 4296, sp + 0x60)] → S'.mem.regions = S.mem.regions →
      S.mem.readLE zzp (8 * n) < M0.readLE mp (8 * n) → ReachesRet (LibW.program.link impl) ret S' Q)
    (KGe : ∀ S' : State, S'.rip = BitVec.ofNat 64 subE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem.readLE (sp - 8) 8 = fnE + 0x1130 → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zzp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 1 = BitVec.ofNat 64 zzc →
      S'.regs 7 = BitVec.ofNat 64 zzp → S'.regs 6 = BitVec.ofNat 64 n → S'.regs 8 = BitVec.ofNat 64 zzc →
      S'.regs 9 = BitVec.ofNat 64 mp → S'.regs 10 = BitVec.ofNat 64 n → S'.regs 11 = BitVec.ofNat 64 mc →
      Mem R b L g sp M0 S'.mem zp zc zzp zzc →
      S'.mem.readLE (sp + 0x188) 8 = zzp → S'.mem.readLE (sp + 0x98) 8 = n → S'.mem.readLE (sp + 0xa0) 8 = zzc →
      S'.mem.readLE zzp (8 * n) = S.mem.readLE zzp (8 * n) →
      MemFrame S.mem S'.mem [(sp - 4296, sp + 0x60)] → S'.mem.regions = S.mem.regions →
      M0.readLE mp (8 * n) ≤ S.mem.readLE zzp (8 * n) → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hst.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  have hn := hst.2.1; have hn16 := hst.2.2.1; have hmc' := hst.2.2.2.2.1
  have hm := hst.2.2.2.2.2.2.2.2.1
  have hzzI := hB.2.1.inp
  have hzzc := hB.2.1.2.1
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tz : (S.regs 0).toNat = zzp := by rw [h0]; exact MontW.toNat_of (by have := hzzI.2.1; omega)
  have tn : (S.regs 3).toNat = n := by rw [h3]; exact MontW.toNat_of (by omega)
  have tm : (S.regs 7).toNat = mp := by rw [h7]; exact MontW.toNat_of (by have := hm.2.1; omega)
  have tn6 : (S.regs 6).toNat = n := by rw [h6]; exact MontW.toNat_of (by omega)
  have hmS : S.mem.readLE mp (8 * n) = M0.readLE mp (8 * n) :=
    FL.read hM.1 hm.2.2.1 hm.2.2.2 hsp1 hB.2.2.2.1 hB.2.2.2.2.1
  have hpre : CmpSum.Pre S := by
    refine ⟨by rw [tsp, hra, fnE_eq]; omega, by omega, by omega, ?_, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [tsp, hM.1.1.accessible]
      exact M0.accessible_sub he.2.2.2.1 (Or.inr rfl) (by omega) (by omega)
    · rw [tz, tn, hM.1.1.accessible]; exact hzzI.1
    · rw [tz, tn, tsp]; have := hzzI.2.2.2; unfold Apart at this ⊢; omega
    · rw [tm, tn6, hM.1.1.accessible]; exact hm.1
    · rw [tm, tn6, tsp]; have := hm.2.2.2; unfold Apart at this ⊢; omega
  refine CmpW.call (cmpSum impl hap) hpc hpre ?_
  intro S' hrip e4 e0 eo exm efs edf hf hrg
  rw [tz, tn, tm, tn6] at e0
  have e5 : S'.regs 5 = r5 := by rw [eo 5 (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  have e14 : S'.regs 14 = BitVec.ofNat 64 g := by
    rw [eo 14 (by decide) (by decide) (by decide) (by decide) (by decide), h14]
  have hws : ∀ r ∈ CmpSum.frame S, sp - 4296 ≤ r.1 ∧ r.2 ≤ sp + 0x60 ∧ r.1 ≤ r.2 := by
    intro r hr
    simp only [CmpSum.frame, tsp, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hM' := Mem.frameW hM he hf hws hrg
  have hfw : MemFrame S.mem S'.mem [(sp - 4296, sp + 0x60)] := by
    refine hf.mono fun a k ho => ?_
    simp only [CmpSum.frame, tsp, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have hrd : ∀ a, sp + 0x60 ≤ a → a + 8 ≤ sp + 0x3c0 → S'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hf.readLE _ _ ?_
    simp only [CmpSum.frame, tsp, outside_cons, outside_nil, and_true]
    omega
  have hzz' : S'.mem.readLE zzp (8 * n) = S.mem.readLE zzp (8 * n) := by
    refine hf.readLE _ _ ?_
    have := hzzI.2.2.2; unfold Apart at this
    simp only [CmpSum.frame, tsp, outside_cons, outside_nil, and_true]
    omega
  have q188 : S'.mem.readLE (sp + 0x188) 8 = zzp := by rw [hrd _ (by omega) (by omega)]; exact r188
  have q98 : S'.mem.readLE (sp + 0x98) 8 = n := by rw [hrd _ (by omega) (by omega)]; exact r98
  have qa0 : S'.mem.readLE (sp + 0xa0) 8 = zzc := by rw [hrd _ (by omega) (by omega)]; exact ra0
  have hrd' := Static.rd hst hM'.1 hB.1 hB.2.1
  have q8 : S'.mem.readLE (sp + 0x3a8) 8 = mp := hrd'.1
  have q0 : S'.mem.readLE (sp + 0x3b0) 8 = n := hrd'.2.1
  have qb : S'.mem.readLE (sp + 0x3b8) 8 = mc := hrd'.2.2.1
  have hrip : S'.rip = BitVec.ofNat 64 (fnE + 0x10d0) := by rw [hrip, retAddrOf_eq, tsp, hra]
  rw [fnE_eq] at hrip
  have e4' : S'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, hsp]; exact sp_add8 (by omega) (by omega)
  clear e4
  have hacc : S'.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
    rw [hM'.1.1.accessible]; exact he.2.2.2.1
  simp only [FvModexp.Asm.lv] at e0; rw [hmS] at e0
  by_cases hlt : S.mem.readLE zzp (8 * n) < M0.readLE mp (8 * n)
  · rw [cmp_lt hlt] at e0
    have hm1 : (18446744073709551615#64 : BitVec 64).msb = true := by decide
    clear hf eo hws hrd
    janus64_run [hm1, q188, q98, qa0, BitVec.msb_eq_decide] until [njoin]
    refine KLt _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfw hrg hlt
    · rw [show njoin = 6210131 by simp only [njoin, fnE_eq]]
    · exact e4'
    · exact e5
    · exact e14
    · rw [efs, hfs]
    · rw [exm, hx15]
    · rfl
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · exact hM'
    · exact hzz'
  · have hge := cmp_ge (n := n) hlt
    clear hf eo hws hrd
    refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 subE) ?_
    janus64_run [hge, q188, q98, qa0, q8, q0, qb] until [subE]
    refine KGe _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega)
    · rfl
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
    · rdw; rw [fnE_eq]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e5
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e14
    · rw [efs, hfs]
    · rw [exm, hx15]
    · rfl
    any_goals (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done)
    · exact Mem.wr hM' he _ (by omega)
    · rdw; exact q188
    · rdw; exact q98
    · rdw; exact qa0
    · have := hzzI.2.2.2; unfold Apart at this
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact hzz'
    · exact hfw.writeLE _ (List.mem_cons_self ..) (by dsimp only; omega) (by dsimp only; omega)
    · simp only [Arm64.Memory.regions_writeLE]; exact hrg

end FvModexp.Amd64.W4Loop
