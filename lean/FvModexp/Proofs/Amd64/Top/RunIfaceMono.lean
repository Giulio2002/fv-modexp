import FvModexp.Proofs.Amd64.Top.RunIface

/-! # `RunIface` (amd64): the three callee specs are monotone in the callee window (as `Arm64.RunIfaceMono`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.RunIface

theorem outside_win_mono {a n : Nat} {s : State} {k a' k' a'' : Nat} (hk : k ≤ k') (ha : a' ≤ a'')
    (h : Outside a n (win s k' a'')) : Outside a n (win s k a') := by
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  omega

theorem callEnv_mono2 {R : RtInv} {L : List (Nat × Nat)} {s : State} {k a k' a' : Nat} (hk : k ≤ k') (ha : a ≤ a')
    (h : CallEnv R L s k' a') : CallEnv R L s k a := by
  obtain ⟨hg, ⟨hb, hA, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨htg, htr, hta⟩⟩ := h
  unfold Apart at hga hta
  refine ⟨⟨hg.noWrap, hg.readable, by have := hg.below; omega⟩, ⟨by omega, by omega,
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)⟩, hal, hd,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgr, fun r hr => outside_win_mono hk ha (hLs r hr), hro,
    ⟨htg, htr, by unfold Apart; omega⟩⟩

theorem globals_mono {R : RtInv} {m : Janus.Arm64.Memory} {s : State} {k a k' a' : Nat} (hk : k ≤ k') (ha : a ≤ a')
    (h : Globals R m (win s k' a')) : Globals R m (win s k a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, outside_win_mono hk ha h10, h11, h12, outside_win_mono hk ha h13⟩

theorem intPre_mono {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {xs : List Nat} {s : State} {k a k' a' : Nat}
    (hk : k ≤ k') (ha : a ≤ a') (h : IntPre R b B L k' a' xs s) : IntPre R b B L k a xs s := by
  obtain ⟨he, hsv, hg, hB, hinv, hx, hp⟩ := h
  refine ⟨callEnv_mono2 hk ha he, hsv, globals_mono hk ha hg, hB, hinv, fun x hx' => ?_, hp⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx x hx'
  exact ⟨h1, outside_win_mono hk ha h2, fun hc => outside_win_mono hk ha (h3 hc), h4, h5, h6, h7⟩

theorem memFrame_win_mono {m m' : Janus.Arm64.Memory} {rt ws : List (Nat × Nat)} {s : State} {k a k' a' : Nat}
    (hk : k ≤ k') (ha : a ≤ a') (h : MemFrame m m' (rt ++ win s k a ++ ws)) : MemFrame m m' (rt ++ win s k' a' ++ ws) :=
  h.mono fun x n hx => by
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h4⟩ := hx
    exact ⟨⟨h1, by omega⟩, h4⟩

theorem intPost_mono {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {z v : Nat} {s s' : State} {k a k' a' : Nat}
    (hk : k ≤ k') (ha : a ≤ a') (h : IntPost R b B L k a z v s s') : IntPost R b B L k' a' z v s s' := by
  obtain ⟨h1, L', b', h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, L', b', h2, h3, h4, h5, h6, memFrame_win_mono hk ha h7, h8⟩

theorem BytesSpec.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : BytesSpec impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : BytesSpec impl R k' a' := fun b L x =>
  (h b L x).mono (fun _ ⟨hp, hl⟩ => ⟨intPre_mono hk ha hp, hl⟩) fun _ _ _ ⟨hfs, hdf, p, n, c, h0, h1, h2, h3, h4, h5, L', b', h6,
    h7, h8, h9, h10, h11⟩ =>
    ⟨hfs, hdf, p, n, c, h0, h1, h2, h3, h4, h5, L', b', h6, h7, h8, h9,
      (memFrame_win_mono (ws := []) hk ha (by simpa using h10)).mono fun _ _ hx => by simpa using hx, h11⟩

theorem ModSpec.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : ModSpec impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ModSpec impl R k' a' := fun b L z y =>
  (h b L z y).mono (fun _ ⟨hp, h1, h2, h3⟩ => ⟨intPre_mono hk ha hp, h1, h2, h3⟩) fun _ _ _ ⟨hfs, hdf, h0, h1, h2⟩ =>
    ⟨hfs, hdf, h0, intPost_mono hk ha h1, h2⟩

theorem oneG_mono {R : RtInv} {L : List (Nat × Nat)} {m : Janus.Arm64.Memory} {xs : List Nat} {s : State}
    {k a k' a' : Nat} (hk : k ≤ k') (ha : a ≤ a') (h : OneG R L m (win s k' a') xs) : OneG R L m (win s k a) xs := by
  obtain ⟨op, ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hx⟩ := h
  exact ⟨op, ⟨h0, h1, h2, h3, h4, h5, outside_win_mono hk ha h6, h7, h8, h9, outside_win_mono hk ha h10⟩, hx⟩

theorem ExpSpec.mono {impl : List Janus.Amd64.Segment} {R : RtInv} {k a k' a' : Nat} (h : ExpSpec impl R k a)
    (hk : k ≤ k') (ha : a ≤ a') : ExpSpec impl R k' a' := fun b L z y mm =>
  (h b L z y mm).mono (fun _ ⟨hp, h1, h2, h3, h4, h5⟩ => ⟨intPre_mono hk ha hp, h1, h2, h3, h4, oneG_mono hk ha h5⟩)
    fun _ _ _ ⟨hfs, hdf, h0, h1⟩ =>
    ⟨hfs, hdf, h0, intPost_mono hk ha h1⟩

end FvModexp.Amd64.RunIface
