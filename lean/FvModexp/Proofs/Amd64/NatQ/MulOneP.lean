import FvModexp.Proofs.Amd64.NatQ.MulOnePre
import FvModexp.Proofs.Amd64.Nat.MulAddWWXA

set_option autoImplicit false

/-!
# [amd64 port (divmc s44) of the Q-form Arm64/NatQ/MulOneP.lean — TIGHT COSTS] `nat.mul` (amd64), `n = 1`: `return z.mulAddWW(x, y[0], 0)` (natmul.go:25-26) — the pure part

`mpost_one`: `MPost` from `mulAddWW`'s `Post ∧ XQ` (callee at `RSP - 264`, window `[RSP-4472, RSP-192)` inside the
caller's `[RSP-W, RSP+88)`), with window-only stores before (`s → S1`) and after (`s2 → s'`) the call.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep stkOK_frame apart_of_held stackBack_keep' inv_frame_win)

theorem bv_of {x : BitVec 64} {p : Nat} (h : x.toNat = p) : x = BitVec.ofNat 64 p := by subst h; simp

/-- an empty range (`e ≤ p`) in a frame's write set writes nothing -/
theorem memFrame_drop_empty {m m' : Memory} {rs : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : MemFrame m m' (rs ++ [(p, e)])) : MemFrame m m' rs :=
  ⟨fun a n ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      have := h.readLE (a + i) 1 (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨ho.of_sub (by omega) (by omega), by omega⟩)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm), h.accessible⟩

theorem liveFrame_drop_empty {m m' : Memory} {L ws : List (Nat × Nat)} {p e : Nat} (he : e ≤ p)
    (h : LiveFrame m m' L (ws ++ [(p, e)])) : LiveFrame m m' L ws :=
  ⟨fun a n hin ho => Janus.Arm64.Memory.readLE_congr (fun i hi => by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := h.readLE (a + i) 1 ⟨r, hr, by omega, by omega⟩ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨ho.of_sub (by omega) (by omega), by omega⟩)
      have h2 : (m.bytes (a + i)).toNat = (m'.bytes (a + i)).toNat := by simpa using this.symm
      exact (BitVec.eq_of_toNat_eq h2).symm)⟩

/-- three frames, the middle one a callee's live frame -/
theorem lf3 {L : List (Nat × Nat)} {s : State} {W : Nat} {m0 m1 m2 m3 : Memory} {ws cs : List (Nat × Nat)}
    (hLs : LiveSep L (win s W 88)) (h1 : MemFrame m0 m1 (win s W 88)) (h2 : LiveFrame m1 m2 L cs)
    (h3 : MemFrame m2 m3 (win s W 88)) (hs : ∀ a n, Outside a n ws → Outside a n cs) : LiveFrame m0 m3 L ws :=
  LiveFrame.trans (LiveFrame.trans (lf_win' ws h1 hLs) (FvModexp.LiveFrame.mono_ws h2 hs) fun _ _ h => h)
    (lf_win' ws h3 hLs) fun _ _ h => h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`MPost` of the `n = 1` path** -/
theorem mpost_one {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W : Nat} {zp zc xp xl : BitVec 64}
    {st xc yp yc : Nat} {y0 : BitVec 64} {s S1 s2 s' : State}
    (hpre : MPre R b H L W zp.toNat zc.toNat st xp.toNat xl.toNat xc yp 1 yc s) (hx1 : xl.toNat ≠ 0)
    (hsp1 : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg1 : S1.regs 14 = s.regs 14)
    (hF1 : MemFrame s.mem S1.mem (win s W 88)) (hy0 : y0.toNat = s.mem.readLE yp 8)
    (hQ : MulAddWW.Post R b L zp zc xp xl y0 0#64 S1 s2 ∧ MulAddWW.XQ R L zp zc xp xl y0 0#64 S1 s2)
    (F3 : MemFrame s2.mem s'.mem (win s W 88)) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (r0 : s'.regs 0 = s2.regs 0) (r3 : s'.regs 3 = s2.regs 3) (r1 : s'.regs 1 = s2.regs 1) :
    MPost R b H L W zp.toNat zc.toNat st xp.toNat xl.toNat xc yp 1 yc s s' := by
  obtain ⟨hce, hmw, -, -, -, hops, hstk, hcost, -, -⟩ := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce
  simp only [regSP] at hb' ha hw
  obtain ⟨⟨-, -, -, -, -, hxw⟩, -, ⟨-, -, hzw, hzs, -, -⟩, -⟩ := hops
  obtain ⟨-, hstok, hstw, -⟩ := hstk
  obtain ⟨⟨-, -, p', n', c', q0, q1, q2, hv, hn, hnc, hnx, L', b', hext, hbud, hinv2, hlive, hkind, hMF, hLF⟩, hc40,
    hkind2, hex⟩ := hQ
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hstok0 := hstok
  obtain ⟨-, hsth, -, -, hsnl, -, -⟩ := hstok0
  have hstA' : Outside st 24 (win s W 88) := hstw
  have hxA : Outside xp.toNat (8 * xl.toNat) (win s W 88) := (hxw (by omega)).1
  have hzA : Outside zp.toNat (8 * zc.toNat) (win s W 88) := hzw
  simp only [win, outside_cons, outside_nil, and_true] at hstw hzw hxA
  rw [q2] at hc40 hkind2
  rw [q0] at hkind2
  have wsub := win_sub (W := W) (ab := 88) (stk1 := 4208) (above1 := 72) hsp1 (by omega) (by omega) (by omega)
  -- frames
  have fz : MemFrame s.mem s'.mem (R.rt ++ win s W 88 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) :=
    frame3 hF1 hMF F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.2, ⟨h.1.1, wsub _ _ h.1.2⟩, h.2⟩
  have lz : LiveFrame s.mem s'.mem L (win s W 88 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) :=
    lf3 hLs hF1 hLF F3 fun a n h => by simp only [outside_append] at h; exact h.2
  -- the stack header is kept (it is apart from `z`, or `z` is empty)
  have hkeep : ∃ ws : List (Nat × Nat), MemFrame s.mem s'.mem (R.rt ++ ws) ∧ LiveFrame s.mem s'.mem L ws ∧
      Outside st 24 ws := by
    by_cases hc : zc.toNat = 0
    · refine ⟨win s W 88, memFrame_drop_empty (by omega) fz, liveFrame_drop_empty (by omega) lz, hstA'⟩
    · have := (hzs (by omega)).2.2.1; unfold Apart at this
      refine ⟨win s W 88 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)], by rw [← List.append_assoc]; exact fz, lz, ?_⟩
      simp only [win, outside_append, outside_cons, outside_nil, and_true]
      omega
  obtain ⟨ws, fws, lws, ows⟩ := hkeep
  have hrd : ∀ k, k + 8 ≤ 24 → s'.mem.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk =>
    Held.readLE (hsth.sub (by omega) (by omega)) fws lws (ows.of_sub (by omega) (by omega))
  have eW : stW s'.mem st = stW s.mem st := by
    simp only [stW]; have := hrd 0 (by omega); simpa using this
  have eC : stCap s'.mem st = stCap s.mem st := by simp only [stCap]; rw [hrd 16 (by omega)]
  -- the result range is outside the caller's window
  have hpo : Outside p' (8 * n') (win s W 88) := by
    simp only [win, outside_cons, outside_nil, and_true]
    rcases hkind with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · omega
    · have := NatAdd.outside_of_inRanges hout hin; omega
  have hxv : natVal S1.mem xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat :=
    natVal_frame hF1 (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hyv : natVal s.mem yp 1 = y0.toNat := by rw [hy0]
  have hval : natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat * natVal s.mem yp 1 := by
    rw [natVal_frame F3 hpo, hv, hxv, hyv]; simp
  refine ⟨hfs, hdf, p', n', c', by rw [r0]; exact bv_of q0, by rw [r3]; exact bv_of q1, by rw [r1]; exact bv_of q2,
    hval, ?_, hnc, by omega, hc40, L', b', hext, ?_, ?_, ?_, ?_, ?_, ?_,
    stackBack_keep' hstok fws lws ows hext,
    frame3 hF1 hMF F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨h.1.1.1, wsub _ _ h.1.1.2⟩, h.1.2⟩,
    lf3 hLs hF1 hLF F3 fun a n h => by simp only [outside_append] at h; exact h.1⟩
  · rcases hn with h | h
    · exact Or.inl h
    · by_cases h0 : n' = 0
      · exact Or.inl h0
      right; rw [F3.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true] at hpo ⊢; omega)]; exact h
  · have h1 := makeCost_need_le' (y := y0) hx1
    have h2 : makeB (xl.toNat + 1) ≤ mulCQ xl.toNat 1 := makeB_le_mulCQ1 hx1
    rw [stkR_congr eC]; have := hcost.2; have := Nat.le_trans h1 h2; omega
  · rw [hg1] at hinv2; exact inv_frame_win F3 hout (by omega) (by decide) hinv2
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hlive hc
    exact ⟨a1, a2, by rw [F3.accessible]; exact a3, a4⟩
  · rcases hkind with h | ⟨hin, hap⟩
    · exact Or.inl h
    · rcases hkind2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', hin, hap⟩
  · intro hne hc0 hcap0
    rcases hkind with h | ⟨hin, hap⟩
    · exact absurd h hne
    rw [eC] at hcap0; rw [eW, eC]
    exact apart_of_held (hsnl hcap0).2.1 hin hap
  · intro h1 _ _
    obtain ⟨e0, e2, hvz, hmf, hlf⟩ := hex h1
    rw [q0] at e0; rw [q2] at e2
    refine ⟨e0, e2, ?_, frame3 hF1 hmf F3 fun a n h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.1.2, ⟨h.1.1.1, wsub _ _ h.1.1.2⟩, h.1.2⟩,
      lf3 hLs hF1 hlf F3 fun a n h => by simp only [outside_append] at h; exact h.1⟩
    have hzo : Outside zp.toNat (8 * (xl.toNat + 1)) (win s W 88) := by
      simp only [win, outside_cons, outside_nil, and_true]; omega
    rw [natVal_frame F3 hzo]
    rcases hvz with hvz | ⟨hy, -, hvz⟩
    · left; rw [hvz, hxv, hyv]; simp
    · right; refine ⟨by rw [hyv, hy]; simp, ?_⟩
      rw [hvz]; exact natVal_frame hF1 hzo

end FvModexp.Amd64.Q.NatMul
