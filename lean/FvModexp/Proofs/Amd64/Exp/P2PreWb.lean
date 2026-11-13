import FvModexp.Proofs.Amd64.Exp.P2PreKeep

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `Ctx` through own stores and the write barrier (agent divmc s62;
adapted from infra's `Arm64/Exp/P2PreWb`)

`PF`: the entry facts every step needs. `ctx_own`: a store into the function's own locals (not a `Sl` slot) or the
`powers` array. `ctx_wb`: the context after `gcWriteBarrier2` and the caller's two stores into its buffer.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep)

/-- the entry facts the steps need -/
structure PF (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl : Nat) (s : State) : Prop where
  w : WinF R kc s st
  ls : LiveSep L (win s (K kc) A)
  pwrt : Outside pw (24 * pl) R.rt
  pww : Outside pw (24 * pl) (win s (K kc) A)
  pwst : Apart pw (24 * pl) st 24
  sp48 : (s.regs 4).toNat + A ≤ 2 ^ 48
  pw48 : pw + 24 * pl ≤ 2 ^ 48

set_option maxRecDepth 20000 in
theorem pf_of {R : RtInv} {kc b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}
    (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 8 ≤ kc) : PF R kc L st pw pl s := by
  have hw := winF_of hpre hkc
  obtain ⟨⟨-, ⟨-, ha, -⟩, -, -, -, -, -, hLs, -⟩, -, -, -, -, -, -, -, hpw48, -, hpwrt, hpww, -, -, ⟨hsa, -⟩, -⟩ := hpre
  exact ⟨hw, hLs, hpwrt, hpww, hsa.symm, ha, hpw48⟩

/-- where the function itself stores: its locals (not the `Sl` slots) and the `powers` array -/
@[reducible] def OwnW (s : State) (pw pl a k : Nat) : Prop :=
  0 < k ∧ (((s.regs 4).toNat - 184 ≤ a ∧ a + k ≤ (s.regs 4).toNat - 48) ∨ ((s.regs 4).toNat - 24 ≤ a ∧ a + k ≤ (s.regs 4).toNat - 8) ∨
    (pw ≤ a ∧ a + k ≤ pw + 24 * pl))

set_option maxRecDepth 20000 in
theorem ctx_own {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State} {bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    (hf : PF R kc L st pw pl s) {a k : Nat} (v : Nat) (ho : OwnW s pw pl a k) :
    Ctx R kc L st pw pl lm x xl s bp (M.writeLE a k v) L1 b1 := by
  have hK := hf.w.sp
  have hrt := hf.w.rt
  have hd := hf.w.hd
  have hpw := hf.pww
  have hpst := hf.pwst
  have hk8 := hf.w.kc8
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hrt hd hpw
  unfold Apart at hpst
  obtain ⟨hk0, ho⟩ := ho
  -- the store is outside `R.rt`
  have hort : Outside a k R.rt := by
    rcases ho with h | h | h
    · exact hrt.of_sub (by omega) (by omega)
    · exact hrt.of_sub (by omega) (by omega)
    · exact hf.pwrt.of_sub (by omega) (by omega)
  -- the store is apart from the stack header
  have hst : st + 24 ≤ a ∨ a + k ≤ st := by rcases ho with h | h | h <;> omega
  have hrd : ∀ b n, st ≤ b → b + n ≤ st + 24 → (M.writeLE a k v).readLE b n = M.readLE b n := fun b n h1 h2 =>
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hW : stW (M.writeLE a k v) st = stW M st := hrd _ _ (Nat.le_refl _) (by omega)
  have hLn : stLen (M.writeLE a k v) st = stLen M st := hrd _ _ (by omega) (by omega)
  have hC : stCap (M.writeLE a k v) st = stCap M st := hrd _ _ (by omega) (by omega)
  obtain ⟨⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩, hl, har⟩ := hc.sa
  refine ⟨?_, ?_, by rw [Janus.Arm64.Memory.regions_writeLE]; exact hc.rg, hc.le, by rw [stkR_congr hC]; exact inv_store_out hc.inv hort,
    ⟨hc.scr.b48, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hc.scr.acc, hc.scr.al, hc.scr.held, hc.scr.loc⟩,
    ⟨⟨ha1, ha2, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact ha3, ha4,
      by rw [hW, hC]; intro h0; obtain ⟨b1, b2, b3, b4⟩ := ha5 h0; exact ⟨b1, b2, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact b3, b4⟩,
      by rw [hLn, hC]; exact ha6, by rw [hC]; exact ha7⟩, by rw [hLn]; exact hl, by rw [hW, hC]; exact har⟩,
    by have := hc.sap; simp only [StkSep, Q.BasicSqr.freeP, Q.BasicSqr.freeN, stW, stLen, stCap] at hW hLn hC this ⊢
       rw [hW, hLn, hC]; exact this,
    ?_, hc.ain.congr hW hC (fun _ h => h), bu_hdr hc.bu hW hLn hC⟩
  · -- the frame
    rcases ho with h | h | h
    · exact hc.fr.writeLE v (r := ((s.regs 4).toNat - K kc, (s.regs 4).toNat + A)) (by simp [AW, win]) (by simp only [K]; omega)
        (by simp only; omega)
    · exact hc.fr.writeLE v (r := ((s.regs 4).toNat - K kc, (s.regs 4).toNat + A)) (by simp [AW, win]) (by simp only [K]; omega)
        (by simp only; omega)
    · exact hc.fr.writeLE v (r := (pw, pw + 24 * pl)) (by simp [AW, LW]) (by simp only; omega) (by simp only; omega)
  · -- the live frame
    refine ⟨fun b n hin hout => ?_⟩
    rw [← hc.lf.readLE b n hin hout]
    refine Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_
    simp only [LW, stkWs, outside_append, outside_cons, outside_nil, and_true] at hout
    obtain ⟨r, hr, h1, h2⟩ := hin
    have hs := hf.ls r hr
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hs
    rcases ho with h | h | h <;> omega
  · -- the slots
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hc.sl
    have hpwa : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := hpw
    have hk : ∀ b, (s.regs 4).toNat ≤ b + 48 → b + 8 ≤ (s.regs 4).toNat + 80 →
        (b + 8 ≤ (s.regs 4).toNat - 24 ∨ (s.regs 4).toNat - 8 ≤ b) →
        (M.writeLE a k v).readLE b 8 = M.readLE b 8 := fun b h1 h2 h3 =>
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by rcases ho with h | h | h <;> omega)
    exact ⟨(hk _ (by omega) (by omega) (by omega)).trans e0, (hk _ (by omega) (by omega) (by omega)).trans e1,
      (hk _ (by omega) (by omega) (by omega)).trans e2, (hk _ (by omega) (by omega) (by omega)).trans e3,
      (hk _ (by omega) (by omega) (by omega)).trans e4, (hk _ (by omega) (by omega) (by omega)).trans e5,
      (hk _ (by omega) (by omega) (by omega)).trans e6, (hk _ (by omega) (by omega) (by omega)).trans e7,
      (hk _ (by omega) (by omega) (by omega)).trans e8, (hk _ (by omega) (by omega) (by omega)).trans e9,
      (hk _ (by omega) (by omega) (by omega)).trans e10⟩

/-- the stack facts survive a step that keeps the header bytes and the accessibility -/
theorem sa_hdr {R : RtInv} {L L1 L2 : List (Nat × Nat)} {st ℓ pl lm bp : Nat} {m0 M M' : Memory}
    (h : StkAfter R L L1 st ℓ pl lm m0 M) (hsap : StkSep M st bp (8 * NB pl lm)) (hLE : LiveExt R L1 L2)
    (hrd : ∀ b n, st ≤ b → b + n ≤ st + 24 → M'.readLE b n = M.readLE b n)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) :
    StkAfter R L L2 st ℓ pl lm m0 M' ∧ StkSep M' st bp (8 * NB pl lm) := by
  have hW : stW M' st = stW M st := hrd _ _ (Nat.le_refl _) (by omega)
  have hLn : stLen M' st = stLen M st := hrd _ _ (by omega) (by omega)
  have hC : stCap M' st = stCap M st := hrd _ _ (by omega) (by omega)
  obtain ⟨⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩, hl, har⟩ := h
  refine ⟨⟨⟨ha1, hLE.held ha2, by rw [hacc]; exact ha3, ha4,
      by rw [hW, hC]; intro h0; obtain ⟨b1, b2, b3, b4⟩ := ha5 h0; exact ⟨b1, hLE.held b2, by rw [hacc]; exact b3, b4⟩,
      by rw [hLn, hC]; exact ha6, by rw [hC]; exact ha7⟩, by rw [hLn]; exact hl, by rw [hW, hC]; exact har⟩, ?_⟩
  simp only [StkSep, Q.BasicSqr.freeP, Q.BasicSqr.freeN, stW, stLen, stCap] at hW hLn hC hsap ⊢; rw [hW, hLn, hC]; exact hsap

/-- `ArrIn` survives a step that keeps the header bytes -/
theorem ain_hdr {R : RtInv} {L1 L2 : List (Nat × Nat)} {st : Nat} {m0 M M' : Memory} (h : ArrIn L1 st m0 M)
    (hrd : ∀ b n, st ≤ b → b + n ≤ st + 24 → M'.readLE b n = M.readLE b n) (hLE : LiveExt R L1 L2) :
    ArrIn L2 st m0 M' :=
  h.congr (hrd _ _ (Nat.le_refl _) (by omega)) (hrd _ _ (by omega) (by omega)) fun _ hr => hLE.mem_old hr

/-- `sa_hdr` with `ArrIn` -/
theorem sa_hdr' {R : RtInv} {L L1 L2 : List (Nat × Nat)} {st ℓ pl lm bp : Nat} {m0 M M' : Memory}
    (hain : ArrIn L1 st m0 M) (hbu : BU M st bp (8 * NB pl lm)) (h : StkAfter R L L1 st ℓ pl lm m0 M)
    (hsap : StkSep M st bp (8 * NB pl lm))
    (hLE : LiveExt R L1 L2) (hrd : ∀ b n, st ≤ b → b + n ≤ st + 24 → M'.readLE b n = M.readLE b n)
    (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) :
    StkAfter R L L2 st ℓ pl lm m0 M' ∧ StkSep M' st bp (8 * NB pl lm) ∧ ArrIn L2 st m0 M' ∧
      BU M' st bp (8 * NB pl lm) :=
  ⟨(sa_hdr h hsap hLE hrd hacc).1, (sa_hdr h hsap hLE hrd hacc).2, ain_hdr hain hrd hLE,
    bu_hdr hbu (hrd _ _ (Nat.le_refl _) (by omega)) (hrd _ _ (by omega) (by omega)) (hrd _ _ (by omega) (by omega))⟩

set_option maxRecDepth 20000 in
/-- (divmc s42) a store into a runtime range apart from the live set keeps the stack capacity -/
theorem rtw_cap {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State} {bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    {a k : Nat} (v : Nat) (hin : InRanges a k R.rt) (hap : ApartAll a k L1) :
    stCap (M.writeLE a k v) st = stCap M st := by
  have hstH := hc.sa.1.2.1
  have hst : st + 24 ≤ a ∨ a + k ≤ st := by
    rcases hstH with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart at this; omega
    · have := hin.apart hO; unfold Apart at this; omega
  exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)

set_option maxRecDepth 20000 in
/-- a store into a runtime range apart from the live set (the write barrier's buffer) -/
theorem ctx_rtw {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State} {bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    (hf : PF R kc L st pw pl s) {a k : Nat} (v : Nat) (hk : 0 < k) (hin : InRanges a k R.rt) (hap : ApartAll a k L1)
    {M0 : Memory} (hM0 : stCap M st = stCap M0 st)
    (hinv : R.inv (b1 + stkR (HP (stLen s.mem st) pl lm) M0 st) L1 (s.regs 14).toNat (view R.rt L1 (M.writeLE a k v))) :
    Ctx R kc L st pw pl lm x xl s bp (M.writeLE a k v) L1 b1 := by
  have hcap := rtw_cap hc v hin hap
  have hK := hf.w.sp
  have hrt := hf.w.rt
  have hk8 := hf.w.kc8
  simp only [K, A] at hK hrt
  have hwin := in_rt_sep (lo := a) (hi := a + k) (by simp only [Nat.add_sub_cancel_left]; exact hin) hrt (by omega)
  have hstH := hc.sa.1.2.1
  have hst : st + 24 ≤ a ∨ a + k ≤ st := by
    rcases hstH with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart at this; omega
    · have := hin.apart hO; unfold Apart at this; omega
  have hsa := sa_hdr (M' := M.writeLE a k v) hc.sa hc.sap (LiveExt.refl R L1)
    (by intro b n h1 h2; apply Janus.Arm64.Memory.readLE_writeLE_of_disjoint; omega)
    (fun _ _ _ => by rw [Janus.Arm64.Memory.accessible_writeLE])
  refine ⟨?_, ?_, by rw [Janus.Arm64.Memory.regions_writeLE]; exact hc.rg, hc.le, by rw [stkR_congr (hcap.trans hM0)]; exact hinv,
    ⟨hc.scr.b48, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hc.scr.acc, hc.scr.al, hc.scr.held, hc.scr.loc⟩,
    hsa.1, hsa.2, ?_, ain_hdr hc.ain (by intro b n h1 h2; apply Janus.Arm64.Memory.readLE_writeLE_of_disjoint; omega)
      (LiveExt.refl R L1), bu_hdr hc.bu (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega))
      (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)) (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega))⟩
  · obtain ⟨r, hr, h1, h2⟩ := hin
    exact hc.fr.writeLE v (r := r) (by simp only [AW, List.mem_append]; exact Or.inl (Or.inl hr)) h1 h2
  · refine ⟨fun b n hb hout => ?_⟩
    rw [← hc.lf.readLE b n hb hout]
    have := hap.apart_of_inRanges (hc.le.inRanges_old hb); unfold Apart at this
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hc.sl
    have hk' : ∀ b, (s.regs 4).toNat - 184 ≤ b → b + 8 ≤ (s.regs 4).toNat + 80 →
        (M.writeLE a k v).readLE b 8 = M.readLE b 8 := fun b h1 h2 =>
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    exact ⟨(hk' _ (by omega) (by omega)).trans e0, (hk' _ (by omega) (by omega)).trans e1,
      (hk' _ (by omega) (by omega)).trans e2, (hk' _ (by omega) (by omega)).trans e3,
      (hk' _ (by omega) (by omega)).trans e4, (hk' _ (by omega) (by omega)).trans e5,
      (hk' _ (by omega) (by omega)).trans e6, (hk' _ (by omega) (by omega)).trans e7,
      (hk' _ (by omega) (by omega)).trans e8, (hk' _ (by omega) (by omega)).trans e9,
      (hk' _ (by omega) (by omega)).trans e10⟩

set_option maxRecDepth 20000 in
/-- **the write barrier**: the context after `gcWriteBarrier2` (called at `S'`, `SP' = SP - 184`) and the caller's two
stores into its buffer -/
theorem ctx_wb {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s S' : State} {bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    (hf : PF R kc L st pw pl s) (hk : 4096 ≤ kc) (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184)
    {m' : Memory} {buf : Nat} (hF : MemFrame M m' (R.rt ++ [((S'.regs 4).toNat - 4096, (S'.regs 4).toNat)]))
    (hLF : LiveFrame M m' L1 []) (hrg : m'.regions = M.regions) (hsl : WbSlots R.rt m' buf 2)
    (hapL : ApartAll buf (8 * 2) L1) (hinvS : InvSlots R (b1 + stkR (HP (stLen s.mem st) pl lm) M st) L1 (s.regs 14).toNat R.rt m' buf 2) (v1 v2 : Nat) :
    Ctx R kc L st pw pl lm x xl s bp ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2) L1 b1 := by
  have hw := hf.w
  have hK := hw.sp
  simp only [K] at hK
  have hF' : MemFrame M m' (R.rt ++ win S' 4096 8 ++ []) := hF.mono fun a n ho => by
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho.1, by omega⟩
  have hrd : ∀ b n, st ≤ b → b + n ≤ st + 24 → m'.readLE b n = M.readLE b n := fun b n h1 h2 => by
    have hd := hw.hd
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hd
    exact rd_keep hw hsp hk (by omega) hF' hLF (hc.sa.1.2.1.sub h1 h2) (by simp only [K, A]; omega) (by simp)
  have hsa := sa_hdr hc.sa hc.sap (LiveExt.refl R L1) hrd hF.accessible
  have hcap1 : stCap m' st = stCap M st := hrd _ _ (by omega) (by omega)
  have hc1 : Ctx R kc L st pw pl lm x xl s bp m' L1 b1 :=
    keepC hc hw hsp hk (by omega) (by simp) hF' hLF hrg (LiveExt.refl R L1) (by rw [stkR_congr hcap1]; exact hinvS.inv) hsa.1 hsa.2
      (ain_hdr hc.ain hrd (LiveExt.refl R L1))
      (bu_hdr hc.bu (hrd _ _ (Nat.le_refl _) (by omega)) (hrd _ _ (by omega) (by omega)) (hrd _ _ (by omega) (by omega)))
  obtain ⟨hbR, hb48, -, -⟩ := hsl
  have hv : ∀ (m : Memory), MemFrame (view R.rt L1 m') (view R.rt L1 m) [(buf, buf + 8 * 2)] →
      R.inv (b1 + stkR (HP (stLen s.mem st) pl lm) M st) L1 (s.regs 14).toNat (view R.rt L1 m) := fun m h => hinvS _ h
  have e1 : view R.rt L1 (m'.writeLE buf 8 v1) = (view R.rt L1 m').writeLE buf 8 v1 :=
    view_writeLE_vis (hbR.sub (a := buf) (n := 8) (Nat.le_refl _) (by omega))
      (Outside.of_sub (a := buf) (n := 8) hapL.outside (Nat.le_refl _) (by omega))
  have e2 : view R.rt L1 ((m'.writeLE buf 8 v1).writeLE (buf + 8) 8 v2) =
      ((view R.rt L1 m').writeLE buf 8 v1).writeLE (buf + 8) 8 v2 := by
    rw [view_writeLE_vis (hbR.sub (a := buf + 8) (n := 8) (by omega) (by omega))
      (Outside.of_sub (a := buf + 8) (n := 8) hapL.outside (by omega) (by omega)), e1]
  have hc2 := ctx_rtw hc1 hf v1 (k := 8) (by omega) (hbR.sub (a := buf) (n := 8) (Nat.le_refl _) (by omega))
    (ApartAll.sub' (a := buf) (n := 8) hapL (Nat.le_refl _) (by omega)) hcap1 (hv _ (by rw [e1]; janus_frame))
  exact ctx_rtw hc2 hf v2 (k := 8) (by omega) (hbR.sub (a := buf + 8) (n := 8) (by omega) (by omega))
    (ApartAll.sub' (a := buf + 8) (n := 8) hapL (by omega) (by omega))
    ((rtw_cap hc1 v1 (hbR.sub (a := buf) (n := 8) (Nat.le_refl _) (by omega))
      (ApartAll.sub' (a := buf) (n := 8) hapL (Nat.le_refl _) (by omega))).trans hcap1) (hv _ (by rw [e2]; janus_frame))

end FvModexp.Amd64.P2Pre
