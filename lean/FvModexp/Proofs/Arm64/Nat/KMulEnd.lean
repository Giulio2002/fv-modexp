import FvModexp.Proofs.Arm64.Nat.KMulEndP
import FvModexp.Proofs.Arm64.Nat.Restore
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the end (natmul.go:217, :250), `KM7 → RET`

`kEnd`: from `KM7` (`0x1bc198`) the `addTo(z[n2:], z1.abs)` call (`kn_addcall`), the defer-bit store, the deferred
closure `karatsuba.deferwrap1` (`kndsum`, pre `knRestPre`), `LDP`/`ADD`/`RET` → `KPost` (`knEndFin`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (IntAt tN' StkSep)

def fnKD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba.deferwrap1"

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore` closure of `karatsuba` as a callee of `LibMul` -/
theorem kndsum (impl : List Segment) :
    Summary (LibMul.program.link impl) (segAddr LibMul.program fnKD) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hr1, hr2, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnKD, reduceSegAddr] at hpc
  janus_run
  refine ⟨rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Memory.readLE_lt s.mem ((s.regs 26).toNat + 16) 8
  omega

theorem kndsum_entry : segAddr LibMul.program fnKD = 0x1bc260 := by decide

/-- the deferred closure's precondition (`Restore.Pre`) at its entry: `R26 = SP - 168` (the defer record), the
memory = `KM`'s plus the defer-bit store -/
theorem knRestPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) (S2 : State)
    (hsp : S2.sp.toNat = s.sp.toNat - 448) (hg : S2.regs 28 = s.regs 28)
    (h26 : (S2.regs 26).toNat = s.sp.toNat - 232) (h30 : S2.regs 30 = BitVec.ofNat 64 0x1bc1c8)
    (hF : MemFrame M S2.mem [(s.sp.toNat - 361, s.sp.toNat - 360)]) : Restore.Pre S2 := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hce := h.callee (S1 := { S2 with mem := M }) (stk1 := 24) (above1 := 0) hsp hg rfl (by omega) (by omega)
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal', hb', ha', hw'⟩, -⟩ := hce
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨hst8, -, hstacc, hst48, -, hslc, -⟩ := h.sok
  have hsl := h.slen
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 361 ∨ s.sp.toNat - 360 ≤ x) → S2.mem.readLE x m = M.readLE x m :=
    fun x m hx => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hgw : S2.mem.readLE ((s.regs 28).toNat + 16) 8 = M.readLE ((s.regs 28).toNat + 16) 8 := by
    unfold Apart at hga; exact hrd _ _ (by omega)
  have hdst : S2.mem.readLE (s.sp.toNat - 232 + 8) 8 = st := by
    rw [hrd _ _ (by omega), show s.sp.toNat - 232 + 8 = s.sp.toNat - 224 by omega]; exact h.dst
  have hdln : S2.mem.readLE (s.sp.toNat - 232 + 16) 8 = stLen s.mem st := by
    rw [hrd _ _ (by omega), show s.sp.toNat - 232 + 16 = s.sp.toNat - 216 by omega]; exact h.dln
  have hcap : S2.mem.readLE (st + 16) 8 = stCap M st := hrd _ _ (by omega)
  have hacc : ∀ a k w, S2.mem.accessible a k w = M.accessible a k w := fun a k w => hF.accessible a k w
  simp only at hg1 hg2 hg3 hal' hb' ha' hw'
  rw [← hg] at hgw
  unfold Restore.Pre GuardOK
  refine ⟨⟨hg1, by rw [hacc]; exact hg2, by rw [hgw]; omega⟩, ⟨hal', hb', ha', by rw [hacc]; exact hw'⟩,
    by rw [h30]; decide, by rw [h30]; decide, by rw [h26]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h26, hacc, h.fr.accessible]
    exact Memory.accessible_sub _ (h.F.env.2.1.2.2.2) (Or.inl rfl) (by omega) (by omega)
  · rw [h26, hdst]; omega
  · rw [h26, hdst, hacc]; exact hstacc
  · rw [h26, hdst, hdln, hcap]; simp only [stLen, stCap] at hsl hslc ⊢; omega
  · rw [h26, hdst, hsp]; unfold Apart; omega
  · rw [h26, hsp]; unfold Apart; omega

/-- **`KPost` at the return**: from `KM` after `addTo` (memory `A`, everything charged), the defer-bit store, the
closure's frame and `len(stk.w)` restored (memory `F`) -/
theorem knEndFin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {A : Memory}
    (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc7 (stLen s.mem st) n) A) {F : Memory}
    (hF : MemFrame A F [(s.sp.toNat - 361, s.sp.toNat - 360), (s.sp.toNat - 472, s.sp.toNat - 456),
      (st + 8, st + 16)])
    (hlen : F.readLE (st + 8) 8 = stLen s.mem st)
    (hz : natVal A zp (2 * n) = natVal s.mem xp n * natVal s.mem yp n) (s' : State) (hs' : s'.mem = F) :
    KPost R b L W st zp (2 * n) xp n yp n s s' := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  have hzw : Outside zp (8 * zc) (win s W 72) := h.F.zw
  have hzs : StkSep s.mem st zp (8 * zc) := h.F.zs
  have hzs1 := hzs.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw hzw
  unfold Apart at hzs1
  have hok := h.sok
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hslc, hsc40⟩ := hok
  have hsl := h.slen
  subst hs'
  have hrd : ∀ x m, Outside x m [(s.sp.toNat - 361, s.sp.toNat - 360), (s.sp.toNat - 472, s.sp.toNat - 456),
      (st + 8, st + 16)] → s'.mem.readLE x m = A.readLE x m := fun x m hx => hF.readLE _ _ hx
  have eW : s'.mem.readLE st 8 = A.readLE st 8 := hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have eC : s'.mem.readLE (st + 16) 8 = A.readLE (st + 16) 8 :=
    hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hzF : natVal s'.mem zp (2 * n) = natVal A zp (2 * n) :=
    hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a k w, s'.mem.accessible a k w = A.accessible a k w := fun a k w => hF.accessible a k w
  refine ⟨hzF.trans hz, Lk, bk, h.ext, ?bud, ?inv, ?sb, ?mf, ?lf⟩
  case bud => have := h.bud; have := kc7_le (stLen s.mem st) n; omega
  case inv =>
    refine RtInv.inv_frame' hF (fun r hr => ?_) h.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; exact hout.of_sub (by omega) (by omega)
    · left; exact hout.of_sub (by omega) (by omega)
    · rcases hsth.sub (a := st + 8) (n := 8) (by omega) (by omega) with h1 | h1
      · right; simpa using h1
      · left; simpa using h1
  case sb =>
    refine ⟨⟨⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, ?_, ?_, ?_⟩, hlen, ?_⟩, ?_⟩
    · show NatLive s'.mem R Lk (s'.mem.readLE st 8) (s'.mem.readLE (st + 16) 8)
      rw [eW, eC]
      intro h0
      obtain ⟨a1, a2, a3, a4⟩ := hnl h0
      exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
    · show s'.mem.readLE (st + 8) 8 ≤ s'.mem.readLE (st + 16) 8
      rw [hlen]; have := eC; simp only [stLen, stCap] at hsl hslc ⊢; omega
    · show s'.mem.readLE (st + 16) 8 < 2 ^ 40
      rw [eC]; exact hsc40
    · show (s'.mem.readLE st 8 = stW s.mem st ∧ s'.mem.readLE (st + 16) 8 = stCap s.mem st) ∨
        (InRanges (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) R.rt ∧
          ApartAll (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) L)
      rw [eW, eC]; exact h.sarr
    · exact h.smem.congr eW eC fun _ h => h
  case mf =>
    refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  case lf =>
    refine ⟨fun x m hin hz => ?_⟩
    rw [hrd x m ?_]
    · exact h.lf.readLE x m hin hz
    · obtain ⟨r, hr, i1, i2⟩ := hin
      have := h.wsep r hr
      simp only [win, stkWs, outside_cons, outside_nil, and_true] at this hz ⊢
      omega

set_option maxRecDepth 20000 in
/-- **The deferred closure call** (at `karatsubaSqr.deferwrap1`'s entry, memory = `KM`'s plus the defer-bit store): the
continuation (at `0x1bc1c8`) gets the saved `X29`/`X30` and `KPost` for every state with its memory -/
theorem kn_restcall (impl : List Segment) (hD : Summary (LibMul.program.link impl) 0x1bc260 Restore.Pre Restore.Post)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {A : Memory}
    (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc7 (stLen s.mem st) n) A)
    (hz : natVal A zp (2 * n) = natVal s.mem xp n * natVal s.mem yp n)
    (S2 : State) (hpc : S2.pc = BitVec.ofNat 64 0x1bc260) (hsp : S2.sp.toNat = s.sp.toNat - 448)
    (hg : S2.regs 28 = s.regs 28) (h26 : (S2.regs 26).toNat = s.sp.toNat - 232)
    (h30 : S2.regs 30 = BitVec.ofNat 64 0x1bc1c8) (hF : MemFrame A S2.mem [(s.sp.toNat - 361, s.sp.toNat - 360)])
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s3 : State, s3.pc = BitVec.ofNat 64 0x1bc1c8 → s3.sp = S2.sp → s3.regs 28 = S2.regs 28 →
      s3.regs 18 = S2.regs 18 → s3.mem.readLE (s.sp.toNat - 456) 8 = (s.regs 29).toNat →
      s3.mem.readLE (s.sp.toNat - 448) 8 = (s.regs 30).toNat →
      (∀ a k w, s3.mem.accessible a k w = A.accessible a k w) →
      (∀ s' : State, s'.mem = s3.mem → KPost R b L W st zp (2 * n) xp n yp n s s') →
      ReachesRet (LibMul.program.link impl) ret s3 Q) :
    ReachesRet (LibMul.program.link impl) ret S2 Q := by
  have hP := knRestPre h S2 hsp hg h26 h30 hF
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 361 ∨ s.sp.toNat - 360 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m hx => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((S2.regs 26).toNat + 8) 8 = st := by
    rw [h26, hrd _ _ (by omega), show s.sp.toNat - 232 + 8 = s.sp.toNat - 224 by omega]; exact h.dst
  have hdln : S2.mem.readLE ((S2.regs 26).toNat + 16) 8 = stLen s.mem st := by
    rw [h26, hrd _ _ (by omega), show s.sp.toNat - 232 + 16 = s.sp.toNat - 216 by omega]; exact h.dln
  refine ReachesRet.call_regions hD hpc hP fun s3 hr hq hreg => ?_
  obtain ⟨q1, q2, q3, -, q5, q6⟩ := hq
  rw [hdst, hdln] at q5
  rw [hdst, hsp] at q6
  have hFF : MemFrame A s3.mem [(s.sp.toNat - 361, s.sp.toNat - 360), (s.sp.toNat - 472, s.sp.toNat - 456),
      (st + 8, st + 16)] :=
    hF.trans q6 fun x m ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hr2 : ∀ x m, s.sp.toNat - 456 ≤ x → x + m ≤ s.sp.toNat - 440 → s3.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact hK s3 (by rw [hr, h30]) q1 q3 q2 ((hr2 _ _ (by omega) (by omega)).trans h.fp)
    ((hr2 _ _ (by omega) (by omega)).trans h.lr) (fun a k w => hFF.accessible a k w) fun s' hs' => knEndFin h hFF q5 hz s' hs'


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kEnd (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} (S : State)
    (hB : KM7 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk l) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    KNGoal impl R b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have hkn : n ≤ 2 * kh n ∧ 2 * kh n ≤ n + 1 := by simp only [kh]; omega
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hl := hB.hl
  have hsp' : (s.sp - 448#64).toNat = s.sp.toNat - 448 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨-, e1, e2, e3⟩ := hB.z1h
  rw [show s.sp.toNat - 264 + 8 = s.sp.toNat - 256 by omega] at e1
  rw [show s.sp.toNat - 264 + 16 = s.sp.toNat - 248 by omega] at e2
  rw [show s.sp.toNat - 264 + 24 = s.sp.toNat - 240 by omega] at e3
  have f3 := hkm.s3; have f1 := hkm.q104; have f4 := hkm.q96; have f5 := hkm.q112
  have hwA : S.mem.accessible (s.sp.toNat - W) (W + 72) true = true := by
    rw [hkm.fr.accessible]; exact hkm.F.env.2.1.2.2.2
  have hsh : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kh n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kh]; omega
  have hsub : ∀ a c : Nat, c ≤ a → a < 2 ^ 64 → BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
    intro a c h1 h2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hD := kndsum impl
  rw [kndsum_entry] at hD
  unfold KNGoal
  janus_run [hsh, f1, f3, f4, f5, e1, e2, e3] until [kAddToA]
  refine kn_addcall impl hap R hmv hB _ rfl ?sp ?g ?m ?ra ?r0 (hsub _ _ (by omega) (by omega))
    ?r2 ?r3 ?r4 ?r5 ?cont
  case cont =>
    intro s2 hpc2 hreg2 hk Lk' bk' hkmA hz
    obtain ⟨k1, k2, k3, k4⟩ := hk
    simp only at k1 k2 k3 k4
    have hp1 := hkmA.dpt
    have hp2 : s2.mem.readLE (s.sp.toNat - 232) 8 = 0x1bc260 := hkmA.dfn
    have hwB : s2.mem.accessible (s.sp.toNat - W) (W + 72) true = true := by
      rw [hkmA.fr.accessible]; exact hkmA.F.env.2.1.2.2.2
    clear hwA f1 f3 f4 f5 e1 e2 e3
    janus_run [hp1, hp2] until [0x1bc260]
    refine kn_restcall impl hD hkmA hz _ rfl ?sp2 ?g2 ?h26 ?h30 ?hF2 ?cont2
    case cont2 =>
      intro s3 q1 q2 q3 q4 hfp hlr hacc3 hpost
      simp only at q2 q3 q4
      have hwC : s3.mem.accessible (s.sp.toNat - W) (W + 72) true = true := by rw [hacc3]; exact hwB
      clear hp1 hp2 hwB
      janus_run [hfp, hlr]
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, hpost _ rfl⟩
      all_goals simp [setReg, q3, q4, k2, k4, h28, h18]
    case hF2 => janus_frame
    all_goals janus_simp
  all_goals janus_simp

end FvModexp.Arm64.NatMul
