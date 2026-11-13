import FvModexp.Proofs.Arm64.ExpQ.SlowQStmt

set_option autoImplicit false

/-!
# Q-form → level-cost bridges (arm64; agent expmc s43, TIGHT COSTS)

A Q-form summary (reserve level `H` ∀-quantified, interface cost `C + stkR H s.mem st`, post
`b − (C + stkR H s.mem st) + stkR H s'.mem st ≤ b'`) gives the level-cost summary (`ExpHyp`/`NHyp` shapes, cost a
function of the entry stack length `ℓ`) with the cost `C + stkRes (ℓ + D)`, `D` the callee's level bound: choose
`H := stLen s.mem st + D` per call (`ens_param`). The reserve is then paid once PER CALL, which is cheap for a
callee called O(1) times per exponentiation (`nat.rem`, `nat.expNNSlow` at `nat.expNN`, the windows' `nat.div`
calls), and keeps every level-cost summary above them (windows, `expNNOdd`, `nat.expNN`, `(*Int).exp`) unchanged.
Loops that call stack users many times (`expNNSlow`'s `sqr`/`mul`/`div`) are converted to the Q-form instead.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q

/-- an `Ensures` for every reserve level gives one whose level is a function of the entry state -/
theorem ens_param {p : Program} {e : Nat} {args : List (BitVec 64)} {pre : Nat → State → Prop}
    {post : Nat → State → State → Prop} {pre' : State → Prop} {post' : State → State → Prop}
    (h : ∀ H, Ensures p e args (pre H) (post H)) (f : State → Nat) (hpre : ∀ s, pre' s → pre (f s) s)
    (hpost : ∀ s s', post (f s) s s' → post' s s') : Ensures p e args pre' post' :=
  fun ret hret s hs hp => (h (f s) ret hret s hs (hpre s hp)).mono fun _ h' => ⟨h'.1, hpost _ _ h'.2⟩

/-- the budget step of a bridge: the Q post with the reserve bounded by `stkRes H` -/
theorem bud_br {b b' C H r r' : Nat} (hr : r ≤ stkRes H) (h : b - (C + r) + r' ≤ b') : b - (C + stkRes H) ≤ b' := by
  omega

/-- the pre's budget of a bridge -/
theorem cost_br {b C H : Nat} {m : Memory} {st : Nat} (h : C + stkRes H ≤ b) : C + stkR H m st ≤ b :=
  Nat.le_trans (Nat.add_le_add_left (stkR_le H m st) C) h

/-- the bridged cost of a callee with level bound `D` -/
@[reducible] def brC (C : Nat → Nat → Nat) (D : Nat → Nat → Nat) (ℓ u v : Nat) : Nat := C u v + stkRes (ℓ + D u v)

/-- the bridged cost of `nat.div` (level bound `16·len u + 64`) -/
@[reducible] def divBr (C : Nat → Nat → Nat) (ℓ ul vl : Nat) : Nat := C ul vl + stkRes (ℓ + 16 * ul + 64)

open FvModexp.Arm64.ExpHyp in
/-- **`nat.div`**: `DivHypLQ` gives `DivHypL` at the cost `C ul vl + stkRes (ℓ + 16·ul + 64)` -/
theorem divL_of_Q {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat} {C : Nat → Nat → Nat}
    (h : DivHypLQ impl R ns stk above C) : DivHypL impl R ns stk above (divBr C) := by
  intro b L z zl zc st z2 z2l z2c u ul uc v vl vc
  refine ens_param (fun H => h H b L z zl zc st z2 z2l z2c u ul uc v vl vc)
    (fun s => stLen s.mem st.toNat + 16 * ul.toNat + 64) (fun s hp => ?_) (fun s s' hq => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, hc, hinv⟩ := hp
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, ⟨Nat.le_refl _, cost_br hc⟩, hinv⟩
  · obtain ⟨q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr, ⟨hLE, hb, hinv⟩, hsb, ha, hf, hl⟩ := hq
    exact ⟨q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr,
      ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, ha, hf, hl⟩

open FvModexp.Arm64.ExpHyp in
/-- **`nat.div`, empty-tolerant**: `DivHypLGQ` gives `DivHypLG` at the bridged cost -/
theorem divLG_of_Q {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat} {C : Nat → Nat → Nat}
    (h : ExpSlow.DivHypLGQ impl R ns stk above C) : ExpSlow.DivHypLG impl R ns stk above (divBr C) := by
  intro b L z zl zc st z2 z2l z2c u ul uc v vl vc
  refine ens_param (fun H => h H b L z zl zc st z2 z2l z2c u ul uc v vl vc)
    (fun s => stLen s.mem st.toNat + 16 * ul.toNat + 64) (fun s hp => ?_) (fun s s' hq => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, hc, hinv⟩ := hp
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, ⟨Nat.le_refl _, cost_br hc⟩, hinv⟩
  · obtain ⟨q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr, ⟨hLE, hb, hinv⟩, hsb, ha, hf, hl, hqr,
      hqa⟩ := hq
    exact ⟨q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr,
      ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, ha, hf, hl, hqr, hqa⟩

namespace CB

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp

/-- `CPre` with a smaller cost -/
theorem cpre_cost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zl zc st : Nat}
    {ins : List (Nat × Nat)} {need c c' : Nat} {s : State} (h : CPre R b L stk above zp zl zc st ins need c s)
    (hc : c' ≤ c) : CPre R b L stk above zp zl zc st ins need c' s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hcb,
    hinv⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    Nat.le_trans hc hcb, hinv⟩

theorem cpostR_of_Q {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zc st v C H : Nat} {s s' : State}
    (h : CPostRQ R b L stk above zp zc st v (C + stkR H s.mem st) (stkR H s'.mem st) s s') :
    CPostR R b L stk above zp zc st v (C + stkRes H) s s' := by
  obtain ⟨p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, hb, hinv⟩, hsb, hf, hl, hrs⟩ := h
  exact ⟨p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, hf, hl, hrs⟩

theorem cpostR0_of_Q {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above zp zc st v C H : Nat} {s s' : State}
    (h : CPostR0Q R b L stk above zp zc st v (C + stkR H s.mem st) (stkR H s'.mem st) s s') :
    CPostR0 R b L stk above zp zc st v (C + stkRes H) s s' := by
  obtain ⟨p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, hb, hinv⟩, hsb, hf, hl, hrs⟩ := h
  exact ⟨p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, hf, hl, hrs⟩

end CB

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp in
/-- **`nat.rem`**: `RemHypQ` gives `RemHyp` at the cost `C ul vl + stkRes (ℓ + need ul vl)` -/
theorem rem_of_Q {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat} {need C : Nat → Nat → Nat}
    (h : RemHypQ impl R ns stk above need C) : RemHyp impl R ns stk above need (brC C need) := by
  intro b L z zl zc st u ul uc v vl vc
  refine ens_param (fun H => h H b L z zl zc st u ul uc v vl vc)
    (fun s => stLen s.mem st.toNat + need ul.toNat vl.toNat) (fun s hp => ?_) (fun s s' hq => CB.cpostR_of_Q hq)
  obtain ⟨⟨hc, hv⟩, hna, hst⟩ := hp
  exact ⟨⟨CB.cpre_cost hc (Nat.add_le_add_left (stkR_le _ s.mem st.toNat) _), hv⟩, hna, hst, Nat.le_refl _⟩

/-- the bridged cost of `nat.expNNSlow` -/
@[reducible] def slowBr (C : Nat → Nat → Nat → Nat) (needH : Nat → Nat → Nat) (ℓ xl yl ml : Nat) : Nat :=
  C xl yl ml + stkRes (ℓ + needH xl ml)

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.NHyp in
/-- **`nat.expNNSlow`**: `SlowHypQ` gives `SlowHyp` at the cost `C xl yl ml + stkRes (ℓ + needH xl ml)` -/
theorem slow_of_Q {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {need : Nat → Nat → Nat → Nat} {needH : Nat → Nat → Nat} {C : Nat → Nat → Nat → Nat}
    (h : SlowHypQ impl R ns stk above need needH C) : SlowHyp impl R ns stk above need (slowBr C needH) := by
  intro b L z zl zc st x xl xc y yl yc m ml mc
  refine ens_param (fun H => h H b L z zl zc st x xl xc y yl yc m ml mc)
    (fun s => stLen s.mem st.toNat + needH xl.toNat ml.toNat) (fun s hp => ?_) (fun s s' hq => CB.cpostR0_of_Q hq)
  obtain ⟨⟨hc, h1, h2, h3, h4⟩, hX⟩ := hp
  exact ⟨⟨CB.cpre_cost hc (Nat.add_le_add_left (stkR_le _ s.mem st.toNat) _), h1, h2, h3, h4⟩, hX, Nat.le_refl _⟩

end FvModexp.Arm64.Q
