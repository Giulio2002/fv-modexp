import FvModexp.Proofs.Amd64.Exp.ModInvSeg3

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the facts inside a Hensel round, and how a callee keeps them
(agent infra s56; twin of `Arm64/Exp/ModInvRnd` + `ModInvKeep`)

`Mid … M L1 b1 p l c q ql qc`: at memory `M` (live set `L1`, invariant at budget `b1`) the spills `Fw2`, the runtime
facts `RtM`, both arrays `z = (p, l, c)` and `zz = (q, ql, qc)` owned and apart, `cap z ≥ numWords + 1`, `cap zz > 0`.
Pure lemmas (address-independent): `x`'s words survive (`x_val`), an owned array stays owned through a callee's
`StackBack` (`own_back`, `stkSep_back`, `wa_back`, `wa_new`), the slots the loop reloads miss every callee window
(`slot_out`; callee `RSP_c = RSP - 232`, window `[RSP_c - stk, RSP_c + above)`, `stk ≤ kc`, `above ≤ 88`), and the
runtime facts survive a callee that writes one owned array (`keep_rt`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep tls guard)

/-- the facts at memory `M` inside a round (see the module doc) -/
@[reducible] def Mid (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (s : State) (zp zc st xp xl xc n : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 p l c q ql qc : Nat) : Prop :=
  Fw2 s M st xp xl xc n ∧ RtM R kc L s zp zc st M L1 b1 ∧
    Own R kc L L1 s zp zc st xp xl M p c ∧ Own R kc L L1 s zp zc st xp xl M q qc ∧
    Apart p (8 * c) q (8 * qc) ∧ l ≤ c ∧ ql ≤ qc ∧ NW n + 1 ≤ c ∧ 0 < qc

/-- a held range keeps its bytes through a frame, checked byte by byte -/
theorem held_bytes {rt L ws1 ws2 : List (Nat × Nat)} {m m' : Memory} {a n : Nat}
    (hh : InRanges a n L ∨ Outside a n rt) (hf : MemFrame m m' (rt ++ ws1 ++ ws2)) (hl : LiveFrame m m' L ws2)
    (h : ∀ i, i < n → Outside (a + i) 1 ws1 ∧ Outside (a + i) 1 ws2) : m'.readLE a n = m.readLE a n := by
  apply Arm64.Memory.readLE_congr
  intro i hi
  have hh1 : InRanges (a + i) 1 L ∨ Outside (a + i) 1 rt :=
    hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega))
  have := Expmc.held_readLE hh1 hf hl (h i hi).1 (h i hi).2
  simp only [Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

set_option maxRecDepth 20000 in
/-- `x`'s words are unchanged at every memory the runtime facts describe -/
theorem x_val {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrt : RtM R kc L s zp zc st M L1 b1) {k : Nat} (hk : k ≤ xl) :
    M.readLE xp (8 * k) = s.mem.readLE xp (8 * k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hxc, -, -, ⟨-, -, -, hxh, hxw⟩, -, -, -, hzx, ⟨-, hst, -⟩, -, -,
    ⟨hsx1, hsx2, -⟩, -⟩ := hpre
  have hlc : stLen s.mem st ≤ stCap s.mem st := hst.2.2.2.2.2.1
  obtain ⟨-, hF, hLF, -⟩ := hrt
  rw [List.append_assoc] at hF
  unfold Apart at hzx hsx1 hsx2
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hxw
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hsx2
  refine held_bytes ((hxh.sub (Nat.le_refl _) (by omega))) hF hLF fun i hi => ⟨?_, ?_⟩
  · simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  · simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨by omega, by omega, by omega⟩

/-- `StkSep` of a range the callee's live set holds, through the callee's `StackBack` -/
theorem stkSep_back {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {M M' : Memory} {a k : Nat}
    (hb : StackBack R L1 L2 st M M') (h : StkSep M st a k) (hh : Held R L1 a k) : StkSep M' st a k := by
  obtain ⟨s1, s2, s3⟩ := h
  obtain ⟨hok, hlen, hor⟩ := hb
  have hlc : stLen M' st ≤ stCap M' st := hok.2.2.2.2.2.1
  refine ⟨s1, ?_, s3⟩
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at s2 ⊢
  rcases hor with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
  · rw [e0, e2, hlen]; exact s2
  · have := fresh_apart hIn hAp hh
    unfold Apart at this ⊢; omega

theorem out_sub {p n a k i j : Nat} {rs : List (Nat × Nat)} (hin : InRanges p n rs) (ho : Outside a k rs)
    (_hij : i ≤ j) (hj : j ≤ n) : Outside a k [(p + i, p + j)] := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem ho hr
  simp only [outside_cons, outside_nil, and_true]; omega

/-- `WA` of an array held by the callee's live set, through the callee's `StackBack` -/
theorem wa_back {R : RtInv} {L1 L2 : List (Nat × Nat)} {zp zc st : Nat} {M M' : Memory} {p c : Nat}
    (hb : StackBack R L1 L2 st M M') (h : WA zp zc st M p c) (hh : 0 < c → Held R L1 p (8 * c)) :
    WA zp zc st M' p c := by
  intro hne hc hcap
  rcases hb.2.2 with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
  · rw [e2] at hcap; rw [e0, e2]; exact h hne hc hcap
  · have := fresh_apart hIn hAp (hh hc); unfold Apart at this ⊢; omega

/-- `WA` of a callee's result: the caller's array reused (`WA` kept), or fresh (callee's apartness conjunct; when
the callee kept the stack's array, that array is held by the callee's entry live set) -/
theorem wa_new {R : RtInv} {L1 L2 : List (Nat × Nat)} {zp zc st : Nat} {M M' : Memory} {t tc t' tc' : Nat}
    (hb : StackBack R L1 L2 st M M') (hok : StkOK M R L1 st) (ht : WA zp zc st M t tc)
    (hth : 0 < tc → Held R L1 t (8 * tc))
    (hof : (t' = t ∧ tc' = tc) ∨ (InRanges t' (8 * tc') R.rt ∧ ApartAll t' (8 * tc') L1))
    (hstkA : ¬ (t' = t ∧ tc' = tc) → 0 < tc' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart t' (8 * tc') (stW M' st) (8 * stCap M' st)) :
    WA zp zc st M' t' tc' := by
  rcases hof with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact wa_back hb ht hth
  by_cases hsame : t' = t ∧ tc' = tc
  · obtain ⟨rfl, rfl⟩ := hsame; exact wa_back hb ht hth
  intro _ hc hcap
  by_cases hk : stW M' st = stW M st ∧ stCap M' st = stCap M st
  · obtain ⟨e0, e2⟩ := hk
    rw [e2] at hcap; rw [e0, e2]
    exact fresh_apart hIn hAp (hok.2.2.2.2.1 hcap).2.1
  · exact hstkA hsame hc hcap hk

/-- an owned (non-empty) array stays owned after a callee: its array is live in the new live set, and the stack
came back -/
theorem own_back {R : RtInv} {kc : Nat} {L L1 L2 : List (Nat × Nat)} {s : State} {zp zc st xp xl : Nat}
    {M M' : Memory} {o oc : Nat} (h : Own R kc L L1 s zp zc st xp xl M o oc) (hoc : 0 < oc)
    (hlive : NatLive M' R L2 o oc) (hsb : StackBack R L1 L2 st M M') : Own R kc L L2 s zp zc st xp xl M' o oc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  exact ⟨a1, a2, hlive, a4, a5, a6, a7, a8, stkSep_back hsb a9 (a3 hoc).2.1,
    wa_back hsb a10 fun hc => (a3 hc).2.1⟩

/-- a callee window at `RSP_c = RSP - 232` (`stk ≤ kc`, `above ≤ 88`) misses every slot at or above `RSP - 144` -/
theorem slot_out {s : State} {kc stk above a : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88)
    (hsp : 232 + kc ≤ (s.regs 4).toNat) {S' : State} (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    (ha : (s.regs 4).toNat - 144 ≤ a) : Outside a 8 (win S' stk above) := by
  simp only [win, hS', outside_cons, outside_nil, and_true]; omega

/-- the callee's writable ranges are inside the function's (arithmetic core of `keep_rt`) -/
theorem keep_ws {rt : List (Nat × Nat)} {sp kc stk above sp' t tc zp zc w0 l0 c0 w l c st : Nat}
    (hS' : sp' = sp - 232) (hstk : stk ≤ kc) (habove : above ≤ 88) (hsp : 232 + kc ≤ sp)
    (ht : (t = zp ∧ tc = zc) ∨ InRanges t (8 * tc) rt) (hlc : l ≤ c)
    (hst : (w = w0 ∧ c = c0 ∧ l = l0) ∨ InRanges w (8 * c) rt) {a k : Nat}
    (h : Outside a k (rt ++ [(sp - (232 + kc), sp + 72)] ++ [(zp, zp + 8 * zc)] ++
      [(st, st + 24), (w0 + 8 * l0, w0 + 8 * c0)])) :
    Outside a k (rt ++ ([(sp' - stk, sp' + above)] ++ ([(t, t + 8 * tc)] ++
      [(st, st + 24), (w + 8 * l, w + 8 * c)]))) := by
  simp only [outside_append] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · simp only [outside_cons, outside_nil, and_true] at h2 ⊢; omega
  · rcases ht with ⟨rfl, rfl⟩ | hIn
    · exact h3
    · simpa using out_sub hIn h1 (Nat.zero_le _) (Nat.le_refl _)
  · simp only [outside_cons, outside_nil, and_true] at h4 ⊢
    refine ⟨h4.1, ?_⟩
    rcases hst with ⟨rfl, rfl, rfl⟩ | hIn
    · exact h4.2
    · have := out_sub hIn h1 (Nat.mul_le_mul_left 8 hlc) (Nat.le_refl _)
      simp only [outside_cons, outside_nil, and_true] at this; exact this

/-- the callee's writable ranges miss the entry's live ranges outside the function's writes -/
theorem keep_wsL {L : List (Nat × Nat)} {sp kc stk above sp' t tc zp zc w0 l0 c0 w l c st : Nat}
    (hS' : sp' = sp - 232) (hstk : stk ≤ kc) (habove : above ≤ 88) (hsp : 232 + kc ≤ sp)
    (hLs : ∀ r ∈ L, Outside r.1 (r.2 - r.1) [(sp - (232 + kc), sp + 72)])
    (ht : (t = zp ∧ tc = zc) ∨ ApartAll t (8 * tc) L)
    (hst : (w = w0 ∧ c = c0 ∧ l = l0) ∨ ApartAll w (8 * c) L) (_hlc : l ≤ c) {a k : Nat} (hin : InRanges a k L)
    (h : Outside a k ([(zp, zp + 8 * zc)] ++ [(st, st + 24), (w0 + 8 * l0, w0 + 8 * c0)])) :
    Outside a k ([(sp' - stk, sp' + above)] ++ ([(t, t + 8 * tc)] ++
      [(st, st + 24), (w + 8 * l, w + 8 * c)])) := by
  obtain ⟨r, hr, hr1, hr2⟩ := hin
  have hrw := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at hrw
  simp only [outside_append] at h ⊢
  obtain ⟨h3, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · rcases ht with ⟨rfl, rfl⟩ | hAp
    · exact h3
    · have := hAp r hr; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true] at h4 ⊢
    refine ⟨h4.1, ?_⟩
    rcases hst with ⟨rfl, rfl, rfl⟩ | hAp
    · exact h4.2
    · have := hAp r hr; unfold Apart at this; omega

/-- `232 + kc ≤ RSP` at the entry -/
theorem sp_K {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) : 232 + kc ≤ (s.regs 4).toNat := by
  have := hpre.1.2.1.1; simp only [regSP, K] at this; omega

set_option maxRecDepth 20000 in
/-- the runtime facts survive a callee (entry `RSP_c = RSP - 232`) that writes the owned array `t` -/
theorem keep_rt {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 b2 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State}
    (hS' : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) {t tc : Nat}
    (ht : Own R kc L L1 s zp zc st xp xl M t tc) (hreg : M'.regions = M.regions)
    (hF : MemFrame M M' (R.rt ++ win S' stk above ++ [(t, t + 8 * tc)] ++ stkWs M st))
    (hLF : LiveFrame M M' L1 ([(t, t + 8 * tc)] ++ stkWs M st)) (hLE : LiveExt R L1 L2)
    (hinv : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 M')) (hsb : StackBack R L1 L2 st M M')
    (hain : ArrIn L2 st M M') : RtM R kc L s zp zc st M' L2 b2 := by
  have hsp := sp_K hpre
  have hLs := hpre.1.2.2.2.2.2.2.2.1
  simp only [LiveSep, win, K, A] at hLs
  have hrt' := hrt
  obtain ⟨-, -, -, -, -, hstk0, len0, arr0, -⟩ := hrt'
  have hlc : stLen M st ≤ stCap M st := hstk0.2.2.2.2.2.1
  have t4 := ht.2.2.2.1
  refine rtM_call hrt hreg (ws := win S' stk above ++ ([(t, t + 8 * tc)] ++ stkWs M st))
    (by simpa only [List.append_assoc] using hF) (fun a k h => ?_)
    ⟨fun a k h ho => hLF.readLE a k h (by simp only [outside_append] at ho ⊢; exact ho.2)⟩ (fun a k hin h => ?_)
    hLE hinv hsb hain
  · simp only [win, stkWs, hS', K, A] at h ⊢
    exact keep_ws rfl hstk habove hsp (t4.imp id fun h => h.1) hlc
      (arr0.imp (fun ⟨e0, e2⟩ => ⟨e0, e2, len0⟩) fun h => h.1) h
  · simp only [win, stkWs, hS'] at h ⊢
    exact keep_wsL rfl hstk habove hsp hLs (t4.imp id fun h => h.2)
      (arr0.imp (fun ⟨e0, e2⟩ => ⟨e0, e2, len0⟩) fun h => h.2) hlc hin h

end FvModexp.Amd64.ModInv
