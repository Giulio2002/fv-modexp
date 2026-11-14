import FvModexp.Proofs.Amd64.Exp.ModInvSeg3

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): runtime-fact lemmas for the loop (agent infra s55; twin of the lemmas of
`Arm64/Exp/ModInvSeg3`)

`frame_bytes`, `own_mono` (an owned array stays owned across accessibility-preserving changes and live-set
extensions), `rtM_store` (a word store into an owned array keeps `RtM`), `dl_rt` (the
read-only data stays loaded), `env_rt` (the call-environment facts at any memory `RtM` describes).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

/-- a frame read byte by byte -/
theorem frame_bytes {m m' : Memory} {rs : List (Nat × Nat)} (hF : MemFrame m m' rs) {a n : Nat}
    (h : ∀ i, i < n → Outside (a + i) 1 rs) : m'.readLE a n = m.readLE a n := by
  apply Arm64.Memory.readLE_congr
  intro i hi
  have := hF.readLE (a + i) 1 (h i hi)
  simp only [Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

/-- an owned array stays owned across a memory change that keeps accessibility and the stack header, and a live-set
extension -/
theorem own_mono {R : RtInv} {kc : Nat} {L L1 L2 : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat} {M M' : Memory}
    {p c : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c) (hLE : LiveExt R L1 L2)
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st) (e2 : stCap M' st = stCap M st) :
    Own R kc L L2 s zp zc st xp xl M' p c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  refine ⟨a1, a2, fun hc => ?_, a4, a5, a6, a7, a8, ?_, ?_⟩
  · obtain ⟨c1, c2, c3, c4⟩ := a3 hc
    exact ⟨c1, hLE.held c2, by rw [hacc]; exact c3, c4⟩
  · simp only [StkSep, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at a9 ⊢; rw [e0, e1, e2]; exact a9
  · unfold WA at a10 ⊢; rw [e0, e2]; exact a10

set_option maxRecDepth 20000 in
/-- a word store into an owned array keeps the runtime facts -/
theorem rtM_store {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p c : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    (hown : Own R kc L L1 s zp zc st xp xl M p c) {a v : Nat} (h1 : p ≤ a) (h2 : a + 8 ≤ p + 8 * c) :
    RtM R kc L s zp zc st (M.writeLE a 8 v) L1 b1 := by
  obtain ⟨r0, F0, LF0, LE0, inv0, stk0, len0, arr0, ain0⟩ := hrt
  obtain ⟨-, -, live, own, -, -, -, -, ⟨sa1, -, -⟩, -⟩ := hown
  obtain ⟨-, hheld, -, -⟩ := live (by omega)
  unfold Apart at sa1
  have hst : Outside st 24 [(a, a + 8)] := by simp only [outside_cons, outside_nil, and_true]; omega
  have hF1 : MemFrame M (M.writeLE a 8 v) [(a, a + 8)] :=
    (MemFrame.refl M _).writeLE_inRanges _ ⟨(a, a + 8), by simp, by simp only; omega, by simp only; omega⟩
  obtain ⟨hstk, e0, e1, e2⟩ := stkOK_frame stk0 hF1 hst (LiveExt.refl R L1)
  have hlen : stLen (M.writeLE a 8 v) st = stLen M st := e1
  refine ⟨by rw [Arm64.Memory.regions_writeLE]; exact r0, ?_, ?_, LE0, inv_store_held inv0 (hheld.sub h1 h2), hstk,
    hlen.trans len0, by rw [e0, e2]; exact arr0, ArrIn.congr ain0 e0 e2 fun _ h => h⟩
  · refine F0.writeLE_inRanges v ?_
    rcases own with ⟨rfl, rfl⟩ | ⟨hIn, -⟩
    · exact ⟨(p, p + 8 * c), List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)),
        by simp only; omega, by simp only; omega⟩
    · exact ((hIn.sub h1 h2).append_left _).append_left _ |>.append_left _
  · rcases own with ⟨rfl, rfl⟩ | ⟨-, hAp⟩
    · exact FvModexp.LiveFrame.writeLE_ws LF0 v ⟨(p, p + 8 * c), List.mem_append_left _ (List.mem_singleton_self _),
        by simp only; omega, by simp only; omega⟩
    · exact LF0.writeLE v (Janus.Contracts.outside_of_forall fun r hr => by
        have := hAp r hr; unfold Apart at this; omega)

set_option maxRecDepth 20000 in
/-- the read-only data is still loaded at a memory the runtime facts describe -/
theorem dl_rt {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) : Extracted.program.DataLoaded M := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, hd, -, -, -, -, hro, -⟩, -, -, -, -, -, -, hzc0, ⟨-, hzlive, -⟩, -, -, -, -, -, -, -,
    -, -, ⟨-, ⟨-, -, hsta, -, hstl, -, -⟩, -⟩, -⟩ := hpre
  obtain ⟨r0, F0, -⟩ := hrt
  refine dataLoaded_frame64 hd r0 hro (by simpa only [List.append_assoc] using F0) ?_
  intro r hr hlt
  simp only [List.mem_append, win, stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [K, A, regSP] at hw hb' ha
  rcases hr with rfl | rfl | rfl | rfl
  · dsimp only [K, A] at hlt ⊢
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · exact Arm64.Memory.accessible_mono _ (hzlive hzc0).2.2.1 (by dsimp only; omega) (by dsimp only; omega)
  · exact Arm64.Memory.accessible_mono _ hsta (by dsimp only; omega) (by dsimp only; omega)
  · dsimp only at hlt ⊢
    exact Arm64.Memory.accessible_mono _ (hstl (by omega)).2.2.1 (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- the call-environment facts at a memory the runtime facts describe: the window writable, the `stackguard0` slot
readable and unchanged, the live set apart from the window -/
theorem env_rt {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) :
    M.accessible ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) true = true ∧
    M.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    LiveSep L1 [((s.regs 4).toNat - (232 + kc), (s.regs 4).toNat + 72)] := by
  obtain ⟨⟨⟨-, hg2, -⟩, ⟨-, -, hw⟩, -, -, hout, hga, hgrt, hLs, -, -⟩, -, -, -, -, -, -, hzc0, ⟨-, -, hzw⟩, -, -, -, -,
    -, -, -, -, -, ⟨-, ⟨-, -, -, -, -, hlc, -⟩, -, hstg, hsta, hfg, -⟩, -⟩ := hpre
  obtain ⟨-, hF, -, hLE, -⟩ := hrt
  obtain ⟨-, hzg, -⟩ := hzw hzc0
  simp only [K, A, regG, stackguard0Offset] at hw hout hga hg2 hLs
  simp only [Q.NatSqr.guard, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hzg hstg hsta hfg
  unfold Apart at hga hzg hstg hfg
  refine ⟨by rw [hF.accessible]; exact hw, by rw [hF.accessible]; exact hg2, ?_, ?_⟩
  · refine frame_bytes hF fun i hi => ?_
    simp only [outside_append, stkWs, win, K, A, outside_cons, outside_nil, and_true]
    refine ⟨⟨⟨hgrt.of_sub (by omega) (by omega), by omega⟩, by omega⟩, by omega, ?_⟩
    omega
  · refine hLE.liveSep (fun q hq => ?_) (fun r hr => ?_)
    · have := hLs q hq
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- a fresh runtime array `(q, c)` (apart from the live set `L0` of `RtM` at `M0`) is owned at a later memory `m`
that keeps the stack header -/
theorem own_fresh {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M0 m : Memory} {L0 L2 : List (Nat × Nat)} {b0 : Nat}
    (hrt : RtM R kc L s zp zc st M0 L0 b0) {q c : Nat} (hc40 : c < 2 ^ 40) (hq : q < 2 ^ 64)
    (hIn : InRanges q (8 * c) R.rt) (hAp0 : ApartAll q (8 * c) L0) (hlive : NatLive m R L2 q c)
    (e0 : stW m st = stW M0 st) (e1 : stLen m st = stLen M0 st) (e2 : stCap m st = stCap M0 st) :
    Own R kc L L2 s zp zc st xp xl m q c := by
  obtain ⟨⟨-, -, -, -, hout, -, hgrt, -, -, ⟨-, htls, -⟩⟩, -, ⟨hgl, -⟩, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, -, hxh, -⟩, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, hfh, -⟩, -⟩ := hpre
  have hgA : Outside RunIface.gA 32 R.rt := hgl.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, LE0, -, hstk, len0, arr0, ain0⟩ := hrt
  have hAp' : ApartAll q (8 * c) L := apartAll_old LE0 hAp0
  have hlc := hstk.2.2.2.2.2.1
  refine ⟨hc40, hq, hlive, Or.inr ⟨hIn, hAp'⟩, ?_, fresh_out hIn hgrt, fresh_out hIn htls,
    fresh_apart hIn hAp0 (LE0.held hxh), ⟨(fresh_apart hIn hAp0 hstk.2.1).symm, ?_, fresh_out hIn hgA⟩, ?_⟩
  · simp only [K, A] at hout
    have := fresh_out hIn hout; unfold Apart at this
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  · simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hfh ⊢
    rw [e0, e1, e2]
    rcases arr0 with ⟨f0, f2⟩ | ⟨-, -⟩
    · rw [len0, f0, f2]; exact fresh_apart hIn hAp0 (LE0.held hfh)
    · by_cases hk : stW M0 st = stW s.mem st ∧ stCap M0 st = stCap s.mem st
      · rw [len0, hk.1, hk.2]; exact fresh_apart hIn hAp0 (LE0.held hfh)
      · obtain ⟨hm, -⟩ := ain0 hk
        have := hAp0 _ hm; unfold Apart at this ⊢; dsimp only at this; omega
  · intro _ _ hcap
    rw [e2] at hcap; rw [e0, e2]
    exact fresh_apart hIn hAp0 (hstk.2.2.2.2.1 hcap).2.1

end FvModexp.Amd64.ModInv
