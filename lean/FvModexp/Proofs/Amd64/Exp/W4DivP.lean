import FvModexp.Proofs.Amd64.Exp.W4Div
import FvModexp.Proofs.Amd64.Exp.W4Cut

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# window-4 prologue (amd64): the facts at the `RR` division's call from the `RR`-section context (`dvPre_of`)
(agent expmc s53; the `hpre` block of `Arm64.W4DivS.divStep`)

Every non-trivial field is a small lemma over explicit facts (no `omega` over the 56-conjunct context).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

/-- the threshold globals for the callee's smaller window `[sp - 8 - stkD, sp - 8 + 112)` -/
theorem globals_win {R : RtInv} {M : Memory} {sp K stkD : Nat}
    (h : RunIface.Globals R M [(sp - 8 - K, sp + 0x3c0)]) (hKD : stkD ≤ K) :
    RunIface.Globals R M [(sp - 8 - stkD, sp - 8 + 112)] := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := h
  simp only [outside_cons, outside_nil, and_true] at g10 g13
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, by simp only [outside_cons, outside_nil, and_true]; omega, g11, g12,
    by simp only [outside_cons, outside_nil, and_true]; omega⟩

/-- a range inside `[b, b + l)` is apart from what is apart from `[b, b + l)` (shrinking the other side to `k'`) -/
theorem apIn {a k b l p q k' : Nat} (h : Apart a k b l) (h1 : b ≤ p) (h2 : p + q ≤ b + l) (hk : k' ≤ k) :
    Apart p q a k' := by
  unfold Apart at h ⊢; omega

/-- a range below the stack's free part is apart from it -/
theorem apFree {p q st : Nat} {M : Memory} (h : p + q ≤ stW M st + 8 * stLen M st) :
    Apart p q (stFree M st).1 (stFree M st).2 := by
  simp only [stFree]; unfold Apart; omega

/-- apart from the whole stack array → apart from its free part -/
theorem arrFree {a k st : Nat} {M : Memory} (h : Apart a k (stW M st) (8 * stCap M st))
    (hlc : stLen M st ≤ stCap M st) : Apart a k (stFree M st).1 (stFree M st).2 := by
  simp only [stFree]; unfold Apart at h ⊢; omega

/-- `q` (fresh, inside the stack's used part above `l0`) ends inside the array -/
theorem q_in_arr {qp n st l0 : Nat} {M : Memory}
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) (hlc : stLen M st ≤ stCap M st) :
    qp + 8 * (2 * n) ≤ (stUp M st l0).1 + (stUp M st l0).2 := by
  simp only [stUp]; omega

/-- `q` lies inside the whole stack array -/
theorem q_whole {qp n st l0 : Nat} {M : Memory}
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) (hlc : stLen M st ≤ stCap M st) :
    stW M st ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stCap M st := by
  omega

theorem zz_len {n zzc : Nat} (hzl : 2 * n + 1 ≤ zzc) : 8 * (2 * n + 1) ≤ 8 * zzc := by omega

theorem zz_sml {n : Nat} (hn : n ≤ 128) : 2 * n + 1 ≤ 2 ^ 9 := by omega

/-- the `RR` scratch's separation from the stack's free part -/
theorem rr_free {rrp n st l0 : Nat} {M : Memory}
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st)) (hlc : stLen M st ≤ stCap M st) :
    Apart rrp (8 * (2 * n)) (stFree M st).1 (stFree M st).2 := by
  rcases hrB with h | h
  · exact apFree h.2
  · exact arrFree h hlc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the division's pre from the context (memory at the call) -/
theorem dvPre_of {R : RtInv} {b : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r stkD qp rrp zzp zzc : Nat} {M : Memory}
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [(rrp, 8 * (2 * n))] M)
    (hZ : ZZ R L g fs sp n mp xp yp ylen zp zc st zzp zzc M) (hzzK : AW sp K zzp (8 * zzc)) (hzl : 2 * n + 1 ≤ zzc)
    (hzN : NatNorm M zzp (2 * n + 1)) (hzzr : Apart zzp (8 * zzc) rrp (8 * (2 * n)))
    (hqin : stW M st + 8 * l0 ≤ qp ∧ qp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st)
    (hqL : NatLive M R L qp (2 * n)) (hqr : Apart qp (8 * (2 * n)) rrp (8 * (2 * n)))
    (hrL : NatLive M R L rrp (2 * n)) (hrW : AW sp K rrp (8 * (2 * n))) (hrG : Apart rrp (8 * (2 * n)) (g + 16) 8)
    (hrF : Apart rrp (8 * (2 * n)) (fs - 8) 8) (hrS : Apart rrp (8 * (2 * n)) st 24)
    (hrB : (stW M st + 8 * l0 ≤ rrp ∧ rrp + 8 * (2 * n) ≤ stW M st + 8 * stLen M st) ∨
      Apart rrp (8 * (2 * n)) (stW M st) (8 * stCap M st))
    (hKD : stkD ≤ K) (hserv : RunIface.Serves R)
    (w0 : M.readLE sp 8 = zzp) (w1 : M.readLE (sp + 8) 8 = 2 * n + 1) (w2 : M.readLE (sp + 16) 8 = zzc)
    (w3 : M.readLE (sp + 24) 8 = mp) (w4 : M.readLE (sp + 32) 8 = n) (w5 : M.readLE (sp + 40) 8 = mc)
    (hsl : stLen M st + 16 * (2 * n + 1) + 64 ≤ 2 ^ 16) (hcF : costF (stLen M st) (2 * n + 1) n ≤ costD)
    (hcb : costD ≤ b) (hinv : R.inv b L g (view R.rt L M)) :
    DvPre R b costF costD L g fs sp K stkD st qp rrp n zzp (2 * n + 1) zzc mp mc M := by
  obtain ⟨-, hce, -, -, hn, hn128, -, -, hm, hmO, -, hnm, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, hcap, harr, hug, huf, huw, hsu, hstg, hstf, hgl, hgO, hstwb, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hstnz⟩ := hC
  obtain ⟨⟨-, -, hzacc, hz48, hzH, -, -, -⟩, -, -, -, -, -, hzS, hzU, -⟩ := hZ
  have hlc : stLen M st ≤ stCap M st := hsok.2.2.2.2.2.1
  have hqa : (stUp M st l0).1 ≤ qp := hqin.1
  have hqb := q_in_arr hqin hlc
  have hz8 := zz_len hzl
  have hex : (rrp, 8 * (2 * n)) ∈ [(rrp, 8 * (2 * n))] := List.mem_singleton_self _
  refine ⟨hce, hKD, hserv, globals_win hgl hKD, hn128, hn, w0, w1, w2, w3, w4, w5,
    hqL, apIn huw.symm hqa hqb (Nat.le_refl _), apIn hug.symm hqa hqb (Nat.le_refl _),
    apIn huf.symm hqa hqb (Nat.le_refl _),
    hrL, hrW, hrG, hrF,
    zz_sml hn128, M.accessible_sub hzacc (Or.inl rfl) (Nat.le_refl _) (Nat.add_le_add_left hz8 _),
    Nat.le_trans (Nat.add_le_add_left hz8 _) hz48, held_sub hzH (Nat.le_refl _) (Nat.add_le_add_left hz8 _),
    Apart.mono hzzK hz8 (Nat.le_refl _),
    hm.1, hm.2.1, hm.2.2.1, hmO.2.1, hzN, hnm, hsok, hstw, fun h => ⟨(harr h).1, (harr h).2.1⟩,
    hsl, hcap, Apart.mono hzS hz8 (Nat.le_refl _),
    Apart.mono (arrFree hzU hlc) hz8 (Nat.le_refl _), hmO.2.2.1, free_of_up hmO.2.2.2.1 hl0 hlc,
    hqr, fun p hp => ?_, apIn hgO.2.2.2.1 hqa hqb (Nat.le_refl _),
    (hgO.2.2.2.2 _ hex).symm, hstnz, hgO.2.2.1.symm, hstg, hstwb, free_of_up hsu hl0 hlc, hstf,
    (free_of_up huf.symm hl0 hlc).symm, (free_of_up hgO.2.2.2.1 hl0 hlc).symm, hcF, hcb, hinv⟩
  rcases hp with rfl | rfl
  · exact ⟨apIn hzU (q_whole hqin hlc).1 (q_whole hqin hlc).2 hz8,
      apIn hmO.2.2.2.1 hqa hqb (Nat.le_refl _), apIn hsu hqa hqb (Nat.le_refl _), apFree hqin.2⟩
  · exact ⟨(Apart.mono hzzr hz8 (Nat.le_refl _)).symm, (hmO.2.2.2.2 _ hex).symm, hrS, rr_free hrB hlc⟩

end FvModexp.Amd64.W4Pro
