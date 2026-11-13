import FvModexp.Proofs.Amd64.NatQ.KMulB

set_option autoImplicit false

/-!
# [amd64 port (divmc s47) of the Q-form Arm64/NatQ/KMulI.lean — TIGHT COSTS] `karatsuba` (amd64): an inner `(*Int).mul` call through the induction hypothesis of the multiplication SCC

`KN.ipre`: the precondition `IPre` of `z.mul(stk, x, y)` (headers in our frame, window `W - 456`, callee at `RSP - 456`) from `KN` and the
facts about the operands' arrays. `kn_icall`: at the entry of `(*Int).mul` (`0x5e29e0`), the call through the
hypothesis below the measure `8n + 2` (continuation gets `Kept`, `IPost`). `kn_icallR`: the exact-write form used by
the three products (`ExactI`: `z`'s array kept, only `z[0:need]` and `z`'s header written) — the continuation gets
`KNAt` at the return address, `KN` (charged `kcI`), the result header and value, and the exact frames.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' tls)
open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)

theorem le_sub456 {a c W : Nat} (h1 : a + 456 ≤ c) (h2 : c ≤ W) : a ≤ W - 456 := by omega

theorem sp_add8K {a c : BitVec 64} (h : a.toNat = c.toNat - 456) (hc : 456 ≤ c.toNat) : a + 8#64 = c - 448#64 := by
  bv_omega

theorem ops_mono {R : RtInv} {L : List (Nat × Nat)} {m : Memory} {g tl : Nat} {ws ws' : List (Nat × Nat)}
    {st zp zc xp xl xc yp yl yc : Nat} (h : Ops R L m g tl ws st zp zc xp xl xc yp yl yc)
    (hs : ∀ a n, Outside a n ws → Outside a n ws') : Ops R L m g tl ws' st zp zc xp xl xc yp yl yc := by
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨y1, y2, y3, y4, y5, y6⟩, ⟨z1, z2, z3, z4, z5, z6⟩, hl⟩ := h
  exact ⟨⟨x1, x2, x3, x4, x5, fun h => ⟨hs _ _ (x6 h).1, (x6 h).2⟩⟩,
    ⟨y1, y2, y3, y4, y5, fun h => ⟨hs _ _ (y6 h).1, (y6 h).2⟩⟩, ⟨z1, z2, hs _ _ z3, z4, z5, z6⟩, hl⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`IPre` of an inner `(*Int).mul`** (`RSP - 456`, window `W - 456`, headers in our frame) -/
theorem KN.ipre (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {S1 : State}
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M)
    (hfs : S1.fsBase = s.fsBase) {z x y : Nat} (hz1 : (s.regs 4).toNat - 328 ≤ z) (hz2 : z + 32 ≤ (s.regs 4).toNat - 16)
    (hx1 : (s.regs 4).toNat - 328 ≤ x) (hx2 : x + 32 ≤ (s.regs 4).toNat - 16)
    (hy1 : (s.regs 4).toNat - 328 ≤ y) (hy2 : y + 32 ≤ (s.regs 4).toNat - 16)
    (hxy : x ≠ y) (hzx : Apart z 32 x 32) (hzy : Apart z 32 y 32) (hnx : hNeg M x ≤ 1) (hny : hNeg M y ≤ 1)
    (hops : Ops R Lk M (s.regs 14).toNat (tls s) (win s W 72) st (hP M z) (hC M z) (hP M x) (hL M x) (hC M x)
      (hP M y) (hL M y) (hC M y))
    (hlx : hL M x ≤ kh n) (hly : hL M y ≤ kh n) (hcost : stLen M st + 4 * (hL M x + hL M y) + 64 ≤ H ∧ mulCQ (hL M x) (hL M y) + stkR H M st ≤ bk) :
    IPre R bk H Lk (W - 456) z st x y S1 := by
  have hzw : Outside (hP M z) (8 * hC M z) (win s W 72) := hops.2.2.1.2.2.1
  have hopsB := IntAS.Box.mk hops
  have hcB := IntAS.Box.mk hcost
  clear hops hcost
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  obtain ⟨hW, hWs, hal, ha48, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have F := h.F
  have htw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - W) (W + 72) := F.env.2.2.2.2.2.2.2.2.2.2.2
  have hgl : Globals R M (win s W 72) := h.glob fun _ _ hx => hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, hwbw⟩ := hgl
  have hwin : ∀ q k, Outside q k (win s W 72) → Outside q k (win S1 (W - 456) 40) :=
    fun q k hq => h.winIn hsp (by omega) (by omega) hq
  have hfw : ∀ q, (s.regs 4).toNat - 328 ≤ q → q + 32 ≤ (s.regs 4).toNat - 16 → Outside q 32 (win S1 (W - 456) 40) := by
    intro q h1 h2; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hstw : Outside st 24 (win s W 72) := F.stk.2.2.1
  have hfrw := h.stk.2.2.1
  simp only [win, outside_cons, outside_nil, and_true, BasicSqr.freeP, BasicSqr.freeN] at hstw hfrw hwbw
  have hhd : ∀ q, (s.regs 4).toNat - 328 ≤ q → q + 32 ≤ (s.regs 4).toNat - 16 → hNeg M q ≤ 1 →
      HdrR R Lk M (win S1 (W - 456) 40) st q := by
    intro q h1 h2 hq
    refine ⟨hq, h.facc false (by omega) (by omega), by omega, hfw q h1 h2, h.frameHeld (by omega) (by omega),
      by unfold Apart; omega, ?_⟩
    simp only [BasicSqr.freeP, BasicSqr.freeN]; unfold Apart; omega
  subst hm
  refine ⟨h.callee hsp hg rfl hfs (by omega) (by omega), le_sub456 (imW64_inner hlx hly) F.hW, F.sv, h.glob hwin, F.wt,
    hxy, hhd x hx1 hx2 hnx, hhd y hy1 hy2 hny, h.facc true (by omega) (by omega), by omega, hfw z hz1 hz2,
    h.frameHeld (by omega) (by omega), by rw [hg]; unfold Apart at hga ⊢; omega,
    by simp only [tls]; rw [hfs]; unfold Apart at htw ⊢; omega,
    by show Apart z 32 RunIface.wbA 4; unfold Apart; omega, hzx, hzy, by unfold Apart; omega, hwbacc,
    fun hc => ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩,
    by rw [hg]; simp only [tls] at hopsB ⊢; rw [hfs]; exact ops_mono hopsB.h hwin,
    h.stkPre hsp hg rfl hfs (by omega) (by omega), hcB.h, by rw [h.fr.accessible]; exact F.adx, by rw [hg]; exact h.inv⟩

end

theorem kn_bud {bk b' c c' : Nat} (h1 : bk - c' ≤ b') (h2 : c' ≤ c) : bk - c ≤ b' := by omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **An inner `(*Int).mul(z, stk, x, y)` call** at its entry (`0x5e29e0`) through the induction hypothesis -/
theorem kn_icall (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat}
    {s : State} {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M)
    (ih : ∀ j, IH impl R H (8 * n + 2) j)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 0x5e29e0) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M) (hfs : S1.fsBase = s.fsBase)
    (hra : S1.mem.readLE (S1.regs 4).toNat 8 < 2 ^ 47) (hx15 : S1.xmm 15 = 0#128) (hdf : S1.df = false)
    {z x y : Nat} (r0 : S1.regs 0 = BitVec.ofNat 64 z) (r1 : S1.regs 3 = BitVec.ofNat 64 st)
    (r2 : S1.regs 1 = BitVec.ofNat 64 x) (r3 : S1.regs 7 = BitVec.ofNat 64 y)
    (hz1 : (s.regs 4).toNat - 328 ≤ z) (hz2 : z + 32 ≤ (s.regs 4).toNat - 16)
    (hx1 : (s.regs 4).toNat - 328 ≤ x) (hx2 : x + 32 ≤ (s.regs 4).toNat - 16)
    (hy1 : (s.regs 4).toNat - 328 ≤ y) (hy2 : y + 32 ≤ (s.regs 4).toNat - 16)
    (hxy : x ≠ y) (hzx : Apart z 32 x 32) (hzy : Apart z 32 y 32) (hnx : hNeg M x ≤ 1) (hny : hNeg M y ≤ 1)
    (hops : Ops R Lk M (s.regs 14).toNat (tls s) (win s W 72) st (hP M z) (hC M z) (hP M x) (hL M x) (hC M x)
      (hP M y) (hL M y) (hC M y))
    (hlx : hL M x ≤ kh n) (hly : hL M y ≤ kh n) (hcost : stLen M st + 4 * (hL M x + hL M y) + 64 ≤ H ∧ mulCQ (hL M x) (hL M y) + stkR H M st ≤ bk)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.rip = retAddrOf S1 → s2.mem.regions = M.regions → Kept S1 s2 →
      IPost R bk H Lk (W - 456) z st x y S1 s2 → ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  have hPi := h.ipre hsp hg hm hfs hz1 hz2 hx1 hx2 hy1 hy2 hxy hzx hzy hnx hny hops hlx hly hcost
  clear hops hcost
  have hb := h.lay
  have h40 := h.F.n40
  have hst : st < 2 ^ 64 := by
    have := h.F.stk.1; have := h.sok.2.2.2.1; omega
  have hz64 : z < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  have hy64 : y < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (ih (.imul, ⟨bk, Lk, W - 456, BitVec.ofNat 64 z, BitVec.ofNat 64 st,
    BitVec.ofNat 64 x, BitVec.ofNat 64 y, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64⟩))
    (by rw [hpc]; rfl) ⟨⟨⟨hra, hx15, hdf, r0, r1, r2, r3⟩, ?_⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · show IPre R bk H Lk (W - 456) (BitVec.ofNat 64 z).toNat (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 x).toNat
      (BitVec.ofNat 64 y).toNat S1
    rw [tN' hz64, tN' hst, tN' hx64, tN' hy64]; exact hPi
  · show μl (hL S1.mem (BitVec.ofNat 64 x).toNat) (hL S1.mem (BitVec.ofNat 64 y).toNat) + 4 < 8 * n + 2
    rw [tN' hx64, tN' hy64, hm]; exact μ_inner h40 hlx hly
  · obtain ⟨hk, hq⟩ := hq
    have hq' : IPost R bk H Lk (W - 456) (BitVec.ofNat 64 z).toNat (BitVec.ofNat 64 st).toNat
        (BitVec.ofNat 64 x).toNat (BitVec.ofNat 64 y).toNat S1 s2 := hq
    rw [tN' hz64, tN' hst, tN' hx64, tN' hy64] at hq'
    exact hK s2 hr (by rw [hreg, hm]) hk hq'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **An inner `(*Int).mul` whose result array is reused** (`need = len x + len y ≤ cap z`, cap ends differ; header
`z` in a writable header area, the written part `[zp', zp' + 8·need)` inside `z[0:2n]` or `t`): the continuation
gets `KN` (charged `kcI`), the result header, value and the exact frames of the call. -/
theorem kn_icallR (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)}
    {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat}
    {M : Memory} (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M)
    (ih : ∀ j, IH impl R H (8 * n + 2) j)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 0x5e29e0) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M) (hfs : S1.fsBase = s.fsBase)
    (hra : S1.mem.readLE (S1.regs 4).toNat 8 < 2 ^ 47) (hx15 : S1.xmm 15 = 0#128) (hdf : S1.df = false)
    {z x y : Nat} (r0 : S1.regs 0 = BitVec.ofNat 64 z) (r1 : S1.regs 3 = BitVec.ofNat 64 st)
    (r2 : S1.regs 1 = BitVec.ofNat 64 x) (r3 : S1.regs 7 = BitVec.ofNat 64 y)
    (hz : ((s.regs 4).toNat - 328 ≤ z ∧ z + 32 ≤ (s.regs 4).toNat - 232) ∨ ((s.regs 4).toNat - 208 ≤ z ∧ z + 32 ≤ (s.regs 4).toNat - 144))
    (hx1 : (s.regs 4).toNat - 328 ≤ x) (hx2 : x + 32 ≤ (s.regs 4).toNat - 16)
    (hy1 : (s.regs 4).toNat - 328 ≤ y) (hy2 : y + 32 ≤ (s.regs 4).toNat - 16)
    (hxy : x ≠ y) (hzx : Apart z 32 x 32) (hzy : Apart z 32 y 32) (hnx : hNeg M x ≤ 1) (hny : hNeg M y ≤ 1)
    (hops : Ops R Lk M (s.regs 14).toNat (tls s) (win s W 72) st (hP M z) (hC M z) (hP M x) (hL M x) (hC M x)
      (hP M y) (hL M y) (hC M y))
    (hlx : hL M x ≤ kh n) (hly : hL M y ≤ kh n)
    (hru : hL M x + hL M y ≤ hC M z) (hnx' : hP M z + 8 * hC M z ≠ hP M x + 8 * hC M x)
    (hny' : hP M z + 8 * hC M z ≠ hP M y + 8 * hC M y)
    (hq : (zp ≤ hP M z ∧ hP M z + 8 * (hL M x + hL M y) ≤ zp + 8 * (2 * n)) ∨
      (t ≤ hP M z ∧ hP M z + 8 * (hL M x + hL M y) ≤ t + 8 * kT n))
    (hsc : spent + kcI n ≤ KCQ n)
    (h5 : S1.regs 5 = s.regs 4 - 8#64) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ra : Nat} (hrv : S1.mem.readLE (S1.regs 4).toNat 8 = ra)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (s2 : State) (Lk' : List (Nat × Nat)) (bk' ng l' : Nat), KNAt s s2 ra →
      s2.mem.regions = M.regions →
      KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' (spent + kcI n) s2.mem →
      IntAt s2.mem z ng (hP M z) l' (hC M z) → ng ≤ 1 → (ng = 1 → 0 < l') →
      sgnV ng (natVal s2.mem (hP M z) l') = intZ M x * intZ M y →
      NatNorm s2.mem (hP M z) l' → l' ≤ hL M x + hL M y →
      (natVal s2.mem (hP M z) (hL M x + hL M y) = natVal M (hP M x) (hL M x) * natVal M (hP M y) (hL M y) ∨
        (natVal M (hP M x) (hL M x) * natVal M (hP M y) (hL M y) = 0 ∧
          natVal s2.mem (hP M z) (hL M x + hL M y) = natVal M (hP M z) (hL M x + hL M y))) →
      MemFrame M s2.mem (R.rt ++ [((s.regs 4).toNat - 456 - (W - 456), (s.regs 4).toNat - 456 + 40)] ++
        [(z, z + 32), (hP M z, hP M z + 8 * (hL M x + hL M y))] ++ stkWs M st) →
      LiveFrame M s2.mem Lk ([(z, z + 32), (hP M z, hP M z + 8 * (hL M x + hL M y))] ++ stkWs M st) →
      ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  have hopsB := IntAS.Box.mk hops
  clear hops
  have hW := h.lay.1
  have hle : mulCQ (hL M x) (hL M y) ≤ kcI n := by
    unfold kcI; exact mulCQ_le_inner hlx hly
  have hcost : stLen M st + 4 * (hL M x + hL M y) + 64 ≤ H ∧ mulCQ (hL M x) (hL M y) + stkR H M st ≤ bk := by
    refine ⟨?_, by have := h.costQ (c := kcI n) hsc; omega⟩
    have e := h.slen; have l := h.F.lvH; have h40 := h.F.n40
    simp only [StackNat.rnd, kT, kh] at e hlx hly; omega
  have hcB := IntAS.Box.mk hcost
  clear hcost hle
  have hz1 : (s.regs 4).toNat - 328 ≤ z := by omega
  have hz2 : z + 32 ≤ (s.regs 4).toNat - 16 := by omega
  refine kn_icall impl R h ih S1 hpc hsp hg hm hfs hra hx15 hdf r0 r1 r2 r3 hz1 hz2 hx1 hx2 hy1 hy2 hxy hzx hzy hnx hny
    hopsB.h hlx hly hcB.h fun s2 hr hreg hk hPo => ?_
  obtain ⟨efs, edf, hval, hng, hcan, hnn, -, hl2, -, L', b', hext, hbud, hinv, -, -, -, hreu, hsb, -, -⟩ := hPo
  rw [hm] at hval hl2 hreu hbud hsb
  have hle0 : mulCQ (hL M x) (hL M y) ≤ kcI n := by
    unfold kcI; exact mulCQ_le_inner hlx hly
  obtain ⟨ep, ec, hv2, hF, hLF⟩ := hreu hru hnx' hny'
  rw [hg] at hinv
  have hkm := h.step (k := W - 456) (a := 40) (by omega) (by omega)
    (ws := [(z, z + 32), (hP M z, hP M z + 8 * (hL M x + hL M y))] ++ stkWs M st) ?ws ?hF hLF hreg hext
    (c := kcI n) (Or.inl (by omega)) hsc hinv hsb
  case ws =>
    intro r hr
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hz with hz | hz
      · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩))⟩
      · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)))⟩
    · rcases hq with hq | hq
      · exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
      · exact ⟨by simp only; omega, Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)⟩
    · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩))))⟩
    · have := h.sok.2.2.2.2.2.1
      exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩))))⟩
  case hF =>
    have hF' := hF
    simp only [win, hsp] at hF'
    rw [List.append_assoc] at hF'
    exact hF'
  have hhd : IntAt s2.mem z (hNeg s2.mem z) (hP M z) (hL s2.mem z) (hC M z) :=
    ⟨rfl, ep, rfl, ec⟩
  have hval' : sgnV (hNeg s2.mem z) (natVal s2.mem (hP M z) (hL s2.mem z)) = intZ M x * intZ M y := by
    rw [← hval]; simp only [sgnV, intZ, ep]
  have hWs := h.lay.2.1
  have e4 : s2.regs 4 = s.regs 4 - 448#64 := by
    rw [hk.1]; exact sp_add8K hsp (by omega)
  have hA : KNAt s s2 ra := ⟨by rw [hr, retAddrOf, hrv], e4, hk.2.2.1.trans hg, hk.2.1.trans h5, efs.trans hfs,
    edf.trans (hdf.trans hdf0.symm), hk.2.2.2.trans (hx15.trans hx150.symm)⟩
  have hF' := hF
  simp only [win, hsp] at hF'
  exact hK s2 L' b' (hNeg s2.mem z) (hL s2.mem z) hA hreg hkm hhd hng hcan hval' (by rw [← ep]; exact hnn) hl2
    hv2 hF' hLF

end FvModexp.Amd64.Q.NatMul
