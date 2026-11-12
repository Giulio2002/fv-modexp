import FvModexp.Proofs.Arm64.Top.RunIface

set_option autoImplicit false

/-! # `RunIface` (arm64): the three callee specs are monotone in the callee window

A spec proved for a window `[SP - stk, SP + above)` holds for every larger window: the precondition at the larger window
implies the one at the smaller (`CallEnv`, `Globals`, the `Outside` facts of the `*Int` objects), and the frame of the
postcondition at the smaller window is inside the larger one. `Run` uses ONE window `(stkM, aboveM)` for `Mod`, `exp`
and `Bytes`: each spec is proved at its own window and lifted here. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.RunIface

theorem outside_win_mono {a n : Nat} {s : State} {k a' k' a'' : Nat} (hk : k ≤ k') (ha : a' ≤ a'')
    (h : Outside a n (win s k' a'')) : Outside a n (win s k a') := by
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  omega

theorem callEnv_mono2 {R : RtInv} {L : List (Nat × Nat)} {s : State} {k a k' a' : Nat} (hk : k ≤ k') (ha : a ≤ a')
    (h : CallEnv R L s k' a') : CallEnv R L s k a := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, hA, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := h
  unfold Apart at hga
  refine ⟨⟨hg1, hg2, by omega⟩, ⟨hal, by omega, by omega, Memory.accessible_mono _ hw (by omega) (by omega)⟩, hd,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgr, fun r hr => outside_win_mono hk ha (hLs r hr), hro⟩

theorem globals_mono {R : RtInv} {m : Memory} {s : State} {k a k' a' : Nat} (hk : k ≤ k') (ha : a ≤ a')
    (h : Globals R m (win s k' a')) : Globals R m (win s k a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, outside_win_mono hk ha h10, h11, h12, outside_win_mono hk ha h13⟩

theorem intPre_mono {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {xs : List Nat} {s : State} {k a k' a' : Nat}
    (hk : k ≤ k') (ha : a ≤ a') (h : IntPre R b B L k' a' xs s) : IntPre R b B L k a xs s := by
  obtain ⟨he, hsv, hg, hB, hinv, hx, hp⟩ := h
  refine ⟨callEnv_mono2 hk ha he, hsv, globals_mono hk ha hg, hB, hinv, fun x hx' => ?_, hp⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx x hx'
  exact ⟨h1, outside_win_mono hk ha h2, fun hc => outside_win_mono hk ha (h3 hc), h4, h5⟩

theorem memFrame_winA_mono {m m' : Memory} {rt ws : List (Nat × Nat)} {s : State} {k a k' a' : Nat} (hk : k ≤ k')
    (ha : a ≤ a') (h : MemFrame m m' (rt ++ winA s k a ++ ws)) : MemFrame m m' (rt ++ winA s k' a' ++ ws) :=
  h.mono fun x n hx => by
    simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
    refine ⟨⟨h1, ?_, ?_⟩, h4⟩ <;> omega

theorem intPost_mono {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {z v : Nat} {s s' : State} {k a k' a' : Nat}
    (hk : k ≤ k') (ha : a ≤ a') (h : IntPost R b B L k a z v s s') : IntPost R b B L k' a' z v s s' := by
  obtain ⟨h1, L', b', h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, L', b', h2, h3, h4, h5, h6, memFrame_winA_mono hk ha h7, h8⟩

theorem BytesSpec.mono {impl : List Segment} {R : RtInv} {k a k' a' : Nat} (h : BytesSpec impl R k a) (hk : k ≤ k')
    (ha : a ≤ a') : BytesSpec impl R k' a' := fun b L x =>
  (h b L x).mono (fun _ ⟨hp, hl⟩ => ⟨intPre_mono hk ha hp, hl⟩) fun _ _ _ ⟨p, n, c, h0, h1, h2, h3, h4, h5, L', b', h6,
    h7, h8, h9, h10, h11⟩ =>
    ⟨p, n, c, h0, h1, h2, h3, h4, h5, L', b', h6, h7, h8, h9,
      (memFrame_winA_mono (ws := []) hk ha (by simpa using h10)).mono fun _ _ hx => by simpa using hx, h11⟩

theorem poolG_mono {R : RtInv} {m : Memory} {s : State} {k a k' a' : Nat} (hk : k ≤ k') (ha : a ≤ a')
    (h : PoolG R m (win s k' a')) : PoolG R m (win s k a) :=
  ⟨h.1, h.2.1, h.2.2.1, outside_win_mono hk ha h.2.2.2⟩

theorem ModSpec.mono {impl : List Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpec impl R k a) (hk : k ≤ k')
    (ha : a ≤ a') : ModSpec impl R k' a' := fun b L z y =>
  (h b L z y).mono (fun _ ⟨hp, h1, h2, h3, h4⟩ => ⟨intPre_mono hk ha hp, h1, h2, h3, poolG_mono hk ha h4⟩) fun _ _ _ ⟨h0, h1, h2⟩ =>
    ⟨h0, intPost_mono hk ha h1, h2⟩

theorem oneG_mono {R : RtInv} {L : List (Nat × Nat)} {m : Memory} {xs : List Nat} {s : State} {k a k' a' : Nat}
    (hk : k ≤ k') (ha : a ≤ a') (h : OneG R L m (win s k' a') xs) : OneG R L m (win s k a) xs := by
  obtain ⟨op, ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hx⟩ := h
  exact ⟨op, ⟨h0, h1, h2, h3, h4, h5, outside_win_mono hk ha h6, h7, h8, h9, outside_win_mono hk ha h10⟩, hx⟩

theorem ExpSpec.mono {impl : List Segment} {R : RtInv} {k a k' a' : Nat} (h : ExpSpec impl R k a) (hk : k ≤ k')
    (ha : a ≤ a') : ExpSpec impl R k' a' := fun b L z y mm =>
  (h b L z y mm).mono (fun _ ⟨hp, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨intPre_mono hk ha hp, h1, h2, h3, h4, oneG_mono hk ha h5, poolG_mono hk ha h6⟩)
    fun _ _ _ ⟨h0, h1⟩ => ⟨h0, intPost_mono hk ha h1⟩

end FvModexp.Arm64.RunIface
