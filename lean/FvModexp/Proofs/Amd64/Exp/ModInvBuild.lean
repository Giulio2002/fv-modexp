import FvModexp.Proofs.Amd64.Exp.ModInvCEnv
import FvModexp.Proofs.Amd64.Exp.ModInvCall

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the callee preconditions inside a round (agent infra s57; twin of
`Arm64/Exp/ModInvBuild` / `ModInvBuild2`)

From the entry `Pre` and the round facts `Mid` at memory `M`, at a callee entry `S'` (`RSP_c = RSP - 232`, `R14` /
`fsBase` the entry's, memory `M`): the preconditions of `zz.sqr(stk, z)` (`sqrPre_mi`, divmc's `Q.NatSqr.SPre`) …
(pure lemmas; window `W ≤ kc`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

/-- the callee's `CallEnv` (window `W ≤ kc`, `above ≤ 304`) -/
theorem callEnv_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase) (hm : S'.mem = M) {W above : Nat} (hW : W ≤ kc)
    (habove : above ≤ 304) : CallEnv R L1 S' W above := by
  have hK := sp_K hpre
  exact CallW.callEnv_of (cenv_mi hpre hrt) hsp (by rw [h14]) (by rw [hfs]) hm hW habove (by omega)

set_option maxRecDepth 20000 in
/-- **`zz = zz.sqr(stk, z)`**: `z = (p, l, c)` is the operand, `zz = (q, ·, qc)` the output -/
theorem sqrPre_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = M) {W : Nat} (hW : W ≤ kc) (hsW : sqrW l ≤ W) (hl : l ≤ NW n + 1)
    (hb : sqrCQ l + stkR H M st ≤ b1) :
    Q.NatSqr.SPre R b1 H L1 W q qc st p l c S' := by
  have hK := sp_K hpre
  have hpre' := hpre
  obtain ⟨-, hsv, -, -, hn2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlen0, -, -, ⟨hD, -⟩, -, hwt, hadx, -⟩ := hpre'
  obtain ⟨-, hrt, hz, hzz, hap, hlc, hqlc, hnc, hqc⟩ := hmid
  have hlen : stLen M st = stLen s.mem st := hrt.2.2.2.2.2.2.1
  have hinv := hrt.2.2.2.2.1
  have hF := hrt.2.1
  obtain ⟨zc40, zp64, zlive, -, zw, zg, zt, -, zsep, -⟩ := hz
  obtain ⟨qc40, -, qlive, -, qw, qg, qt, -, qsep, -⟩ := hzz
  have hsub : ∀ {a k : Nat}, Outside a k (win s (K kc) A) → Outside a k (win S' W 64) :=
    fun h => win_mi hK hsp hW (by omega) h
  have hgd : guard S' = guard s := by simp only [Q.NatSqr.guard]; rw [h14]
  have htd : tls S' = tls s := by simp only [Q.NatSqr.tls]; rw [hfs]
  have hc0 : 0 < c := by omega
  obtain ⟨-, -, zacc, z48⟩ := zlive hc0
  have hnw : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  subst hm
  refine ⟨callEnv_mi hpre hrt hsp h14 hfs rfl hW (by omega), hsW, hsv, globals_mi hpre hrt hsp hW (by omega), hwt,
    hlc, zc40, by omega, S'.mem.accessible_sub zacc (Or.inl rfl) (Nat.le_refl _) (by omega),
    fun _ => ⟨(zlive hc0).2.1, z48⟩, fun _ => hsub (zw.of_sub (Nat.le_refl _) (by omega)), qc40, qlive, hsub qw,
    fun _ => ⟨by rw [hgd]; exact qg, by rw [htd]; exact qt, qsep⟩, Or.inr fun _ _ => by unfold Apart at hap ⊢; omega,
    stkPre_mi hpre hrt hsp h14 hfs rfl hW (by omega),
    fun _ => ⟨?_, ?_, ?_⟩, by rw [hlen]; simp only [D] at hD; omega,
    ⟨by rw [hlen]; simp only [D] at hD; omega, hb⟩, by rw [hF.accessible]; exact hadx, by rw [h14]; exact hinv⟩
  · have := zsep.1; unfold Apart at this ⊢; omega
  · have := zsep.2.1; unfold Apart at this ⊢; omega
  · have := zsep.2.2; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- `StkSep` of a range held at entry, at a memory with the runtime facts -/
theorem stkSep_rt {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    {a k : Nat} (h : StkSep s.mem st a k) (hh : Held R L a k) : StkSep M st a k := by
  obtain ⟨s1, s2, s3⟩ := h
  obtain ⟨-, -, -, -, -, hok, hlen, hor, -⟩ := hrt
  have hlc : stLen M st ≤ stCap M st := hok.2.2.2.2.2.1
  refine ⟨s1, ?_, s3⟩
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at s2 ⊢
  rcases hor with ⟨e0, e2⟩ | ⟨hIn, hAp⟩
  · rw [e0, e2, hlen]; exact s2
  · have := fresh_apart hIn hAp hh
    unfold Apart at this ⊢; omega

theorem stkSep_sub'' {M : Memory} {a k a' k' : Nat} (h : StkSep M st a k) (h1 : a ≤ a') (h2 : a' + k' ≤ a + k) :
    StkSep M st a' k' := by
  obtain ⟨s1, s2, s3⟩ := h
  unfold Apart at s1 s2 s3
  exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩

theorem stkSep_sub' {M : Memory} {a k k' : Nat} (h : StkSep M st a k) (hk : k' ≤ k) : StkSep M st a k' := by
  obtain ⟨s1, s2, s3⟩ := h
  unfold Apart at s1 s2 s3
  exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩

set_option maxRecDepth 20000 in
/-- **`zz = zz.mul(stk, zz, x[:k])`**: `zz = (q, ql, qc)` is output and first operand, `y = x[:k] = (xp, k, xc)` on
the stack -/
theorem mulPre_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = M) {W : Nat} (hW : W ≤ kc) {k : Nat} (hmW : mulW64 ql k ≤ W) (hk : k ≤ xl)
    (hqk : ql + k ≤ 2 * NW n + 2) (hb : mulCQ ql k + stkR H M st ≤ b1) :
    Q.NatMul.MPre R b1 H L1 W q qc st q ql qc xp k xc S' := by
  have hK := sp_K hpre
  have hpre' := hpre
  obtain ⟨-, hsv, -, -, hn2, -, -, -, -, -, -, hxc40, -, ⟨-, hxacc, -, -, hxw⟩, -, -, ⟨hxh, hx48⟩, -, -, -, -, hsx,
    ⟨hD, -⟩, -, hwt, hadx, -⟩ := hpre'
  obtain ⟨-, hrt, -, hzz, -, -, hqlc, -, hqc⟩ := hmid
  have hlen : stLen M st = stLen s.mem st := hrt.2.2.2.2.2.2.1
  have hinv := hrt.2.2.2.2.1
  have hF := hrt.2.1
  have hLE := hrt.2.2.2.1
  obtain ⟨qc40, -, qlive, -, qw, qg, qt, qx, qsep, -⟩ := hzz
  have hsub : ∀ {a k : Nat}, Outside a k (win s (K kc) A) → Outside a k (win S' W 88) :=
    fun h => win_mi hK hsp hW (by omega) h
  have hgd : (S'.regs 14).toNat = (s.regs 14).toNat := by rw [h14]
  have htd : tls S' = tls s := by simp only [Q.NatSqr.tls]; rw [hfs]
  obtain ⟨-, qh, qacc, q48⟩ := qlive hqc
  have hnw : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hxw
  have hsxM := stkSep_rt hrt hsx (hxh.sub (Nat.le_refl _) (by omega))
  have hxk : M.accessible xp (8 * k) false = true := by
    rw [hF.accessible]; exact s.mem.accessible_sub hxacc (Or.inl rfl) (Nat.le_refl _) (by omega)
  subst hm
  refine ⟨callEnv_mi hpre hrt hsp h14 hfs rfl hW (by omega), hmW, hsv, globals_mi hpre hrt hsp hW (by omega), hwt,
    ⟨⟨hqlc, qc40, by omega, fun _ => S'.mem.accessible_sub qacc (Or.inl rfl) (Nat.le_refl _) (by omega),
      fun _ => ⟨qh, q48⟩, fun _ => ⟨hsub (qw.of_sub (Nat.le_refl _) (by omega)), stkSep_sub' qsep (by omega)⟩⟩,
      ⟨by omega, hxc40, by omega, fun _ => hxk,
      fun _ => ⟨hLE.held hxh, hx48⟩, fun _ => ⟨?_, stkSep_sub' hsxM (by omega)⟩⟩,
      ⟨qc40, qlive, hsub qw, fun _ => ⟨by rw [hgd]; exact qg, by rw [htd]; exact qt, qsep⟩, Or.inl ⟨rfl, rfl⟩,
        Or.inr fun _ _ => by unfold Apart at qx ⊢; omega⟩, by rw [hlen]; simp only [D] at hD; omega⟩,
    stkPre_mi hpre hrt hsp h14 hfs rfl hW (by omega),
    ⟨by rw [hlen]; simp only [D] at hD; omega, hb⟩, by rw [hF.accessible]; exact hadx, by rw [h14]; exact hinv⟩
  simp only [win, hsp, outside_cons, outside_nil, and_true]; omega

/-- an owned array as a callee's output -/
theorem wrOut_mi {M : Memory} {L1 : List (Nat × Nat)} {p c : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    (hK : 232 + kc ≤ (s.regs 4).toNat) {S' : State} (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase) (hm : S'.mem = M) {stk above : Nat}
    (hstk : stk ≤ kc) (habove : above ≤ 304) : WrOut R L1 S' stk above p c := by
  obtain ⟨h1, -, h3, -, h5, h6, h7, -⟩ := h
  simp only [WrOut]
  rw [hm, h14, hfs]
  exact ⟨h1, h3, fun _ => ⟨win_mi hK hsp hstk habove h5, h6, h7⟩⟩

/-- an owned array (`len ≤ cap`, `cap > 0`) as a callee operand -/
theorem rdIn_mi {M : Memory} {L1 : List (Nat × Nat)} {p c l : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    (hc : 0 < c) (hl : l ≤ c) (hK : 232 + kc ≤ (s.regs 4).toNat) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc)
    (habove : above ≤ 304) : RdIn R L1 S' stk above p l := by
  obtain ⟨h1, -, h3, -, h5, -⟩ := h
  obtain ⟨-, c2, c3, c4⟩ := h3 hc
  simp only [RdIn]
  rw [hm]
  exact ⟨by omega, M.accessible_sub c3 (Or.inr rfl) (Nat.le_refl _) (by omega), by omega,
    c2.sub (Nat.le_refl _) (by omega), win_mi hK hsp hstk habove (h5.of_sub (Nat.le_refl _) (by omega))⟩

set_option maxRecDepth 20000 in
/-- **`zz = zz.trunc(zz, e)`** -/
theorem truncPre_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 304) {e : Nat} (he : e ≤ 2 ^ 20)
    (hql : ql ≤ 2 ^ 16) (hb : makeCost (truncNeed ql e) ≤ b1) :
    TruncPre R b1 L1 stk above q ql qc q ql e S' := by
  have hK := sp_K hpre
  obtain ⟨-, hrt, -, hzz, -, -, hqlc, -, hqc⟩ := hmid
  have hinv := hrt.2.2.2.2.1
  exact ⟨callEnv_mi hpre hrt hsp h14 hfs hm hstk habove, hpre.2.1, hqlc, wrOut_mi hzz hK hsp h14 hfs hm hstk habove,
    rdIn_mi hzz hqc hqlc hK hsp hm hstk habove, hql, he, Or.inl rfl, hb, by rw [h14, hm]; exact hinv⟩

set_option maxRecDepth 20000 in
/-- **`z = z.lsh(z, 1)`** -/
theorem lshPre_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 304) (hl : l ≤ NW n + 1)
    (hb : makeCost (l + 1 / 64 + 1) ≤ b1) :
    Lsh.LshPreA R b1 L1 stk above p l c p l 1 S' := by
  have hK := sp_K hpre
  have hn2 := hpre.2.2.2.2.1
  obtain ⟨-, hrt, hz, -, -, hlc, -, hnc, -⟩ := hmid
  have hinv := hrt.2.2.2.2.1
  have hnw : NW n ≤ 2 ^ 9 := by simp only [NW]; omega
  exact ⟨callEnv_mi hpre hrt hsp h14 hfs hm hstk habove, hpre.2.1, hlc, wrOut_mi hz hK hsp h14 hfs hm hstk habove,
    rdIn_mi hz (by omega) hlc hK hsp hm hstk habove, by omega, Or.inl rfl, hb, by rw [h14, hm]; exact hinv⟩

set_option maxRecDepth 20000 in
/-- a held range outside the function's writes (window, `z`, the stack's writable parts) keeps its bytes -/
theorem held_mi {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1)
    {a k : Nat} (hh : Held R L a k) (hw : Outside a k (win s (K kc) A)) (hz : Apart zp (8 * zc) a k)
    (hs : StkSep s.mem st a k) : M.readLE a k = s.mem.readLE a k := by
  obtain ⟨-, hF, hLF, -⟩ := hrt
  rw [List.append_assoc] at hF
  obtain ⟨hs1, hs2, -⟩ := hs
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hs2
  unfold Apart at hz hs1 hs2
  refine held_bytes hh hF hLF fun i hi => ⟨?_, ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true] at hw ⊢; omega
  · simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨by omega, by omega, by omega⟩

/-- an owned array apart from a range the entry holds, when the caller's array is -/
theorem own_apart {M : Memory} {L1 : List (Nat × Nat)} {p c a k : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    (hh : Held R L a k) (hz : Apart zp (8 * zc) a k) : Apart p (8 * c) a k := by
  rcases h.2.2.2.1 with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact hz
  · exact fresh_apart hIn hAp hh

set_option maxRecDepth 20000 in
/-- `natOne` at a round callee's entry (window `[RSP_c - K, RSP_c + 88)`, `K ≤ kc`) -/
theorem natOne_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {op : Nat}
    (hone : NatOne R L s.mem op (win s (K kc) A) ∧ Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
      StkSep s.mem st op 8 ∧ StkSep s.mem st natOneA 24) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) {W above : Nat} (hW : W ≤ kc) (habove : above ≤ 304) :
    NatOne R L1 M op (win S' W above) := by
  obtain ⟨⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩, za, zo, so, sa⟩ := hone
  have hK := sp_K hpre
  have hLE := hrt.2.2.2.1
  have hF := hrt.2.1
  have hrd : ∀ j, j + 8 ≤ 24 → M.readLE (natOneA + j) 8 = s.mem.readLE (natOneA + j) 8 := fun j hj =>
    held_mi hrt (Or.inr (nrt.of_sub (by omega) (by omega))) (nwin.of_sub (by omega) (by omega))
      (by unfold Apart at za ⊢; omega) (stkSep_sub'' sa (by omega) (by omega))
  have hO : M.readLE op 8 = s.mem.readLE op 8 := held_mi hrt oh ow zo so
  refine ⟨by rw [show natOneA = natOneA + 0 from rfl, hrd 0 (by omega)]; exact n0, by rw [hrd 8 (by omega)]; exact n8,
    by rw [hrd 16 (by omega)]; exact n16, by rw [hO]; exact nw, by rw [hF.accessible]; exact na, nrt,
    win_mi hK hsp hW habove nwin, by rw [hF.accessible]; exact oa, o48, hLE.held oh, win_mi hK hsp hW habove ow⟩

set_option maxRecDepth 20000 in
/-- **`z = z.subMod2N(z, zz, e)`** (`z = (p, l, c)`, `y = zz = (q, ql, qc)`, `e` at `RSP_c + 8`) -/
theorem subPre_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hkc : SubMod2N.K ≤ kc) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 p l c q ql qc : Nat} (hmid : Mid R kc L s zp zc st xp xl xc n M L1 b1 p l c q ql qc)
    {op : Nat}
    (hone : NatOne R L s.mem op (win s (K kc) A) ∧ Apart zp (8 * zc) natOneA 24 ∧ Apart zp (8 * zc) op 8 ∧
      StkSep s.mem st op 8 ∧ StkSep s.mem st natOneA 24)
    {S' : State} (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232) (h14 : S'.regs 14 = s.regs 14)
    (hfs : S'.fsBase = s.fsBase) (hm : S'.mem = M)
    {e : Nat} (he1 : 1 ≤ e) (he : e ≤ 2 ^ 15) (hl : l ≤ 2 ^ 12) (hql : ql ≤ 2 ^ 12)
    (hnz : NatNorm M p l) (hnq : NatNorm M q ql) (hb : SubMod2N.cost e ≤ b1 ∧ (c < SubMod2N.W e → SubMod2N.costG e ≤ b1))
    (hra : M.readLE (S'.regs 4).toNat 8 < 2 ^ 47) (hen : M.readLE ((S'.regs 4).toNat + 8) 8 = e)
    (hx15 : S'.xmm 15 = 0) (hdf : S'.df = false) :
    SubMod2N.PreG R b1 L1 op p l c q ql qc e S' := by
  have hK := sp_K hpre
  have hone' := hone
  obtain ⟨⟨-, -, -, -, -, nrt, -, -, -, oh, -⟩, za, zo, -, -⟩ := hone'
  obtain ⟨-, hrt, hz, hzz, hap, hlc, hqlc, hnc, hqc⟩ := hmid
  have hz' := hz
  obtain ⟨c40, p64, zlive, -, zwin, zg, zt, -⟩ := hz'
  obtain ⟨q40, q64, qlive, -, qwin, -, -, -⟩ := hzz
  obtain ⟨-, qh, qa, q48⟩ := qlive hqc
  have hsub : ∀ {a k : Nat}, Outside a k (win s (K kc) A) → Outside a k (win S' SubMod2N.K SubMod2N.A) :=
    fun h => win_mi hK hsp hkc (by decide) h
  subst hm
  refine ⟨callEnv_mi hpre hrt hsp h14 hfs rfl hkc (by decide), hpre.2.1, hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    natOne_mi hpre hrt hone hsp hkc (by decide), own_apart hz (Or.inr nrt) za, own_apart hz oh zo, he1, he, hlc,
    ⟨p64, q64⟩, c40, hl, hqlc, q40, hql, zlive, hsub zwin, by rw [h14]; exact zg, hnz,
    fun _ => S'.mem.accessible_sub qa (Or.inr rfl) (Nat.le_refl _) (by omega), fun _ => by omega,
    fun _ => qh.sub (Nat.le_refl _) (by omega), fun _ => hsub (qwin.of_sub (Nat.le_refl _) (by omega)), hnq,
    fun _ _ => hap, hb, by rw [h14]; exact hrt.2.2.2.2.1, ⟨by rw [hfs]; exact zt, hra, hen, hx15, hdf⟩⟩

end

end FvModexp.Amd64.ModInv
