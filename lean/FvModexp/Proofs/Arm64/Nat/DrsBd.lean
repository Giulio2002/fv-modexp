import FvModexp.Proofs.Arm64.Nat.DrsSNP

/-!
# `divRecursiveStep` (arm64), big path: the relations of one loop iteration (no janus runs)

Every body/final-block segment module imports this module (ROW-TIME lesson).

* `IOut s rs`: `rs` avoids the iteration slots (`j - B` at `SP-104`, `uu = u[j-B:]` as ptr `SP-88`, len `SP-288`,
  cap `SP-280`); `scrI s` = the own scratch slots minus the iteration slots.
* `Bd c s M j Z`: the memory facts fixed during the iteration `j` (fixed slots `Sl`, the iteration slots, `v` and the
  tail `u[u1:ul]` as at the entry, `z` as at the iteration start `Z`); `Bd.frame` (survives a frame avoiding them).
* `Ev.callN` / `Fp.hdr`: the environment and the free part after a callee that does not allocate (same live set) and
  does not touch the stack header.
* `A1`: the state after `clear(qhat)` of a loop iteration (`0x1ba558`, the return of the memclr call).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- `rs` avoids the iteration slots -/
@[reducible] def IOut (s : State) (rs : List (Nat × Nat)) : Prop :=
  Outside (s.sp.toNat - 104) 8 rs ∧ Outside (s.sp.toNat - 88) 8 rs ∧ Outside (s.sp.toNat - 288) 16 rs

/-- the own scratch slots without the iteration slots -/
@[reducible] def scrI (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 392, s.sp.toNat - 297), (s.sp.toNat - 296, s.sp.toNat - 288), (s.sp.toNat - 272, s.sp.toNat - 224),
    (s.sp.toNat - 200, s.sp.toNat - 184), (s.sp.toNat - 168, s.sp.toNat - 152), (s.sp.toNat - 144, s.sp.toNat - 104),
    (s.sp.toNat - 96, s.sp.toNat - 88), (s.sp.toNat - 80, s.sp.toNat - 64), (s.sp.toNat - 32, s.sp.toNat - 16)]

theorem fixOut_scrI {s : State} (h : 408 ≤ s.sp.toNat) : FixOut s (scrI s) ∧ IOut s (scrI s) := by
  simp only [FixOut, IOut, scrI, outside_cons, outside_nil, and_true]; omega

/-- a callee frame `R.rt ++ winA S k a ++ ws` (`S.sp = SP - 400`, `a ≤ 103`) avoids the iteration slots when `ws`
does -/
theorem iOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside (s.sp.toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - 400) (ha : a ≤ 103) (hws : IOut s ws) :
    IOut s (R.rt ++ winA S k a ++ ws) := by
  obtain ⟨w1, w2, w3⟩ := hws
  have o : ∀ x n, s.sp.toNat - 408 ≤ x → x + n ≤ s.sp.toNat + 96 → Outside x n R.rt :=
    fun x n h1 h2 => hout.of_sub (by omega) (by omega)
  simp only [IOut, winA, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  exact ⟨⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w1⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w2⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w3⟩⟩

/-- the memory facts fixed during the iteration `j` (`Z` = the quotient at the iteration start) -/
structure Bd (c : Cx) (s : State) (M : Memory) (j : Nat) (Z : List Nat) : Prop where
  sl : Sl c s M
  sj : M.readLE (s.sp.toNat - 104) 8 = j - c.vl / 2
  sup : M.readLE (s.sp.toNat - 88) 8 = c.up + 8 * (j - c.vl / 2)
  sul : M.readLE (s.sp.toNat - 288) 8 = c.u1 - (j - c.vl / 2)
  suc : M.readLE (s.sp.toNat - 280) 8 = c.uc - (j - c.vl / 2)
  vk : M.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)
  utl : M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  zk : Asm.limbs M c.qp c.ql = Z

theorem Bd.frame {c : Cx} {s : State} {M M' : Memory} {j : Nat} {Z : List Nat} {rs : List (Nat × Nat)}
    (h : Bd c s M j Z) (hF : MemFrame M M' rs) (ho : FixOut s rs) (hi : IOut s rs)
    (hv : M'.readLE c.vp (8 * c.vl) = M.readLE c.vp (8 * c.vl))
    (hu : M'.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)))
    (hz : M'.readLE c.qp (8 * c.ql) = M.readLE c.qp (8 * c.ql)) : Bd c s M' j Z := by
  obtain ⟨i1, i2, i3⟩ := hi
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N → M'.readLE x n = M.readLE x n :=
    fun hA h1 h2 => hF.readLE _ _ (hA.of_sub h1 h2)
  exact ⟨h.sl.frame hF ho, by rw [r i1 (by omega) (by omega)]; exact h.sj, by rw [r i2 (by omega) (by omega)]; exact h.sup,
    by rw [r i3 (by omega) (by omega)]; exact h.sul, by rw [r i3 (by omega) (by omega)]; exact h.suc,
    by rw [hv]; exact h.vk, by rw [hu]; exact h.utl, by rw [limbs_congr hz]; exact h.zk⟩

/-- a write into a `Loc` range (the entry stack's free part, or a fresh runtime block) is inside the entry's
caller-visible writes and avoids the entry live set outside them -/
theorem Loc.out {R : RtInv} {c : Cx} {s : State} {a n : Nat} (h : Loc R c s a n) :
    (∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k [(a, a + n)]) ∧
      (∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k [(a, a + n)]) := by
  rcases h with ⟨h1, h2⟩ | ⟨hin, hap⟩
  · refine ⟨fun x k ho => ?_, fun x k _ ho => ?_⟩
    · simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · simp only [Cx.ws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  · refine ⟨fun x k ho => ?_, fun x k hx _ => ?_⟩
    · simp only [outside_append] at ho
      have := FvModexp.Arm64.NatAdd.outside_of_inRanges ho.1.1 hin
      simp only [outside_cons, outside_nil, and_true]; omega
    · obtain ⟨r, hr, h1, h2⟩ := hx
      have := hap r hr; unfold Apart at this
      simp only [outside_cons, outside_nil, and_true]; omega

/-- a held range outside the window and a callee's writes `ws` keeps its bytes over a callee frame
(`X.sp = SP - 400`, callee stack `winA X k a` inside the window) -/
theorem keepRd {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {M M' : Memory} {k0 a0 x n : Nat}
    {ws : List (Nat × Nat)} (hcr : Cr R c s) (hX : X.sp.toNat = s.sp.toNat - 400) (hk : k0 + 400 ≤ c.W) (ha : a0 ≤ 400)
    (hF : MemFrame M M' (R.rt ++ winA X k0 a0 ++ ws)) (hL : LiveFrame M M' Lk ws) (hh : Held R Lk x n)
    (hw : Outside x n (win s c.W 96)) (ho : Outside x n ws) : M'.readLE x n = M.readLE x n := by
  refine Held.readLE2 hh hF hL ?_ ho
  have := hcr.pre.1.2.1.2.1
  simp only [win, winA, outside_cons, outside_nil, and_true] at hw ⊢
  rw [hX]; omega

/-- the header of the stack object avoids `R.rt`-or-live callee writes: it is held and outside the window -/
theorem hdr_keep {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory}
    {wsS ws : List (Nat × Nat)} (hcr : Cr R c s) (h : Ev R c s Lk bk M)
    (hF : MemFrame M M' (R.rt ++ wsS ++ ws)) (hL : LiveFrame M M' Lk ws)
    (hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k wsS) (hst : Outside c.st 24 ws) :
    stW M' c.st = stW M c.st ∧ stLen M' c.st = stLen M c.st ∧ stCap M' c.st = stCap M c.st := by
  have hW := hcr.hW; have := drsW_ge c.vl
  obtain ⟨-, hsto, -, -⟩ := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsh : Held R Lk c.st 24 := h.sok.2.1
  have hw : Outside c.st 24 wsS := hS _ _ (by
    simp only [win, winA, outside_cons, outside_nil, and_true] at hsto ⊢; omega)
  have k : ∀ x n, c.st ≤ x → x + n ≤ c.st + 24 → M'.readLE x n = M.readLE x n := fun x n h1 h2 =>
    Held.readLE2 (hsh.sub h1 h2) hF hL (hw.of_sub h1 h2) (hst.of_sub h1 h2)
  exact ⟨k _ _ (by omega) (by omega), k _ _ (by omega) (by omega), k _ _ (by omega) (by omega)⟩

/-- **the environment after a non-allocating callee** (live set kept; new budget `bk'`) -/
theorem Ev.callN {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk bk' : Nat} {M M' : Memory}
    {wsS ws : List (Nat × Nat)} (hcr : Cr R c s) (h : Ev R c s Lk bk M)
    (hF : MemFrame M M' (R.rt ++ wsS ++ ws)) (hL : LiveFrame M M' Lk ws)
    (hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k wsS)
    (hW1 : ∀ x k, Outside x k (R.rt ++ winA s c.W 96 ++ c.ws s) → Outside x k ws)
    (hW2 : ∀ x k, InRanges x k c.L → Outside x k (c.ws s) → Outside x k ws) (hst : Outside c.st 24 ws)
    (hinv : R.inv bk' Lk (s.regs 28).toNat (view R.rt Lk M')) (hreg : M'.regions = M.regions) :
    Ev R c s Lk bk' M' := by
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr h hF hL hS hst
  have hfr : MemFrame M M' (R.rt ++ winA s c.W 96 ++ c.ws s) := hF.mono fun x k ho => by
    have h1 := hW1 x k ho
    simp only [outside_append] at ho ⊢
    exact ⟨⟨ho.1.1, hS x k ho.1.2⟩, h1⟩
  have hext := h.ext
  refine ⟨h.ext, by rw [hreg]; exact h.reg, hinv, mf_trans h.fr hfr, ?_,
    stkOK_moveS h.sok eW eL eC hF.accessible, by rw [eW, eC]; exact h.sarr⟩
  refine ⟨fun x k hin ho => ?_⟩
  rw [hL.readLE x k ?_ (hW2 x k hin ho)]
  · exact h.lf.readLE x k hin ho
  · exact (hcr.ext1.trans hext).inRanges_old hin

/-- the guard word is the entry one at every memory of the environment -/
theorem Ev.grd {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hcr : Cr R c s) (h : Ev R c s Lk bk M) : M.readLE (grd s) 8 = s.mem.readLE (grd s) 8 := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, hqg⟩, ⟨-, -, -, -, hug⟩, -, -, -, -,
    ⟨-, -, hstg, harr⟩, ⟨-, hc0, -⟩, -⟩ := hcr.pre
  obtain ⟨-, -, -, -, hga, hgr, -, -⟩ := hce
  obtain ⟨-, hag⟩ := harr hc0
  refine h.fr.readLE _ _ ?_
  unfold Apart at hga hqg hug hstg hag
  unfold DivRec.grd
  simp only [Cx.ws, stkWs, winA, outside_append, outside_cons, outside_nil, and_true]
  and_intros <;> first | exact hgr | omega

/-- a read inside a range whose whole read is unchanged is unchanged -/
theorem rd_sub {m m' : Memory} {a N x k : Nat} (h : m'.readLE a N = m.readLE a N) (h1 : a ≤ x) (h2 : x + k ≤ a + N) :
    m'.readLE x k = m.readLE x k := by
  have e : N = (x - a) + (k + (a + N - (x + k))) := by omega
  have ex : a + (x - a) = x := by omega
  rw [e, Memory.readLE_add, Memory.readLE_add, Memory.readLE_add (m := m), Memory.readLE_add (m := m), ex] at h
  obtain ⟨-, h3⟩ := Asm.split_unique (Memory.readLE_lt _ _ _) (Memory.readLE_lt _ _ _) h
  exact (Asm.split_unique (Memory.readLE_lt _ _ _) (Memory.readLE_lt _ _ _) h3).1

/-- the free part with the stack header unchanged -/
theorem Fp.hdr {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {M M' : Memory} {lM : Nat}
    (h : Fp R c s Lk M lM) (eW : stW M' c.st = stW M c.st) (eL : stLen M' c.st = stLen M c.st)
    (eC : stCap M' c.st = stCap M c.st) : Fp R c s Lk M' lM := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  rw [← eW, ← eC] at h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨by rw [eL]; exact h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- the divisor as a list -/
@[reducible] def Cx.V (c : Cx) (s : State) : List Nat := Asm.limbs s.mem c.vp c.vl

/-- the loop invariant of `divRecursiveStep` at `j` on the lists `Z`, `U` -/
@[reducible] def Cx.LI (c : Cx) (s : State) (j : Nat) (Z U : List Nat) : Prop :=
  Mdl.LI (c.V s) c.vl (c.vl / 2) (c.u1 - c.vl) c.ql (natVal s.mem c.up c.u1) j Z U

/-! ## after `clear(qhat)` -/

/-- the return address of the `clear(qhat)` call of the loop body -/
abbrev r1 : Nat := 0x1ba558

/-- **after `clear(qhat)`** (iteration `j`, `Z`/`U` = quotient/dividend at the iteration start) -/
structure A1 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 r1
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  bd : Bd c s S.mem j Z
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  uk : Asm.limbs S.mem c.up c.u1 = U
  q0 : S.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0
  bud : (j / (c.vl / 2) + 1) * c.K s ≤ bk

end FvModexp.Arm64.DivRec
