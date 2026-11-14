import FvModexp.Proofs.Amd64.Exp.SlowLN
import FvModexp.Proofs.Amd64.Exp.SlowMv
import FvModexp.Proofs.Amd64.Exp.SlowPR

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the context `JC`, the prologue joins `KS` (`setJ`) / `KV` (`aSet`) (agent expmc s79;
twin of arm64 `SlowJ`/`SlowPK`/`SlowPV`'s structures, the frame facts of asm's amd64 `EvJ`)

* `JC`: `RSP = sp`, `R14 = g`, `fs`, `X15 = 0`, `DF` clear, the context `WC` at the entry level, the constant slots
  `ESl`. `JC.call` (through a callee keeping the slots), `JC.own` (`WC`, every `DL`/`LN` through the function's own
  stores `OwnR`).
* `KS` (at `setJ`): `z`'s array chosen (`DL`, `len x ≤ cap`), registers as `runJ` needs them; `dl_reuse` (the entry
  `z`) / `dl_fresh` (a `makeslice` array). `KV` (at `aSet`): `z = x` (`LN`), registers as the `v`/`w` setup needs them.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- the return state of a call (`res` results) -/
theorem rs_regs {T : State} {junk : Nat → W64} {res : List W64} {f : Flags} {x yh : Nat → BitVec 128} {m : Memory}
    {zh : Nat → BitVec 256} {kr : Nat → W64} :
    (retState64 T junk res f x yh m zh kr).regs 4 = T.regs 4 + 8#64 ∧
      (retState64 T junk res f x yh m zh kr).regs 14 = T.regs 14 ∧
      (retState64 T junk res f x yh m zh kr).fsBase = T.fsBase ∧
      (retState64 T junk res f x yh m zh kr).xmm 15 = T.xmm 15 ∧
      (retState64 T junk res f x yh m zh kr).df = T.df ∧
      (retState64 T junk res f x yh m zh kr).rip = retAddrOf T ∧
      (retState64 T junk res f x yh m zh kr).mem = m := by
  simp [retState64, callRegs64_apply]

theorem rs_r0 {T : State} {junk : Nat → W64} {ptr : W64} {f : Flags} {x yh : Nat → BitVec 128} {m : Memory}
    {zh : Nat → BitVec 256} {kr : Nat → W64} : (retState64 T junk [ptr] f x yh m zh kr).regs 0 = ptr := by
  simp [retState64, callRegs64_apply]

theorem ra_eq {T : State} {sp ra : Nat} (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8)) (hsp : sp < 2 ^ 64)
    (hra : T.mem.readLE (sp - 8) 8 = ra) : retAddrOf T = BitVec.ofNat 64 ra := by
  rw [retAddrOf_eq, h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hra]

theorem bv_add8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 (sp - 8) + 8#64 = BitVec.ofNat 64 sp := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem bv_of_toNat {x : W64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- the context at every point after the prologue (`RSP = sp`) -/
structure JC (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  esp : S.regs 4 = BitVec.ofNat 64 sp
  e14 : S.regs 14 = BitVec.ofNat 64 g
  efs : S.fsBase.toNat = fs
  ex15 : S.xmm 15 = 0
  edf : S.df = false
  wc : WC R L K g sp st zp zc s.mem S.mem L1 b1 (stLen s.mem st)
  esl : ESl S.mem sp st bp r zp xp xl xc yp yl yc mp ml mc

/-- at `setJ` (`fnE + 0xda`) -/
structure KS (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 pZ cZ : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  pc : S.rip = BitVec.ofNat 64 setJ
  dz : DL R L st zp zc S.mem L1 pZ cZ
  lz : xl ≤ cZ
  r0 : S.regs 0 = BitVec.ofNat 64 pZ
  r1 : S.regs 1 = BitVec.ofNat 64 cZ
  r2 : S.regs 2 = BitVec.ofNat 64 xl
  r8 : S.regs 8 = BitVec.ofNat 64 xl
  r6 : S.regs 6 = BitVec.ofNat 64 xp
  r7 : S.regs 7 = BitVec.ofNat 64 st
  r9 : S.regs 9 = BitVec.ofNat 64 xc

/-- at `aSet` (`fnE + 0x148`): `z` (a copy of `x`) in `(AX, R10, CX)` -/
structure KV (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s S : State) (L1 : List (Nat × Nat)) (b1 pZ cZ : Nat) : Prop where
  jc : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1
  pc : S.rip = BitVec.ofNat 64 aSet
  bz : LN R L st zp zc S.mem L1 pZ xl cZ (natVal s.mem xp xl)
  r0 : S.regs 0 = BitVec.ofNat 64 pZ
  r1 : S.regs 1 = BitVec.ofNat 64 cZ
  r2 : S.regs 2 = BitVec.ofNat 64 xl
  r10 : S.regs 10 = BitVec.ofNat 64 xl
  r6 : S.regs 6 = BitVec.ofNat 64 xp
  r7 : S.regs 7 = BitVec.ofNat 64 st
  r9 : S.regs 9 = BitVec.ofNat 64 xc

/-- `JC` through a step keeping `RSP`/`R14`/`fs`/`X15`/`DF` and the slots `[sp + 0x1a8, sp + 0x220)` -/
theorem JC.call {R : RtInv} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s S : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (h : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1) {S' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat}
    (esp : S'.regs 4 = S.regs 4) (e14 : S'.regs 14 = S.regs 14) (efs : S'.fsBase = S.fsBase)
    (ex15 : S'.xmm 15 = S.xmm 15) (edf : S'.df = S.df)
    (hw : WC R L K g sp st zp zc s.mem S'.mem L2 b2 (stLen s.mem st))
    (hk : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → S'.mem.readLE a k = S.mem.readLE a k) :
    JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 :=
  ⟨esp.trans h.esp, e14.trans h.e14, by rw [efs]; exact h.efs, ex15.trans h.ex15, edf.trans h.edf, hw,
    h.esl.keep (fun a k ha => hk a k ha.1 ha.2)⟩

/-- a store range of the function's own frame -/
@[reducible] def OwnR (sp K : Nat) (r : Nat × Nat) : Prop :=
  r.1 ≤ r.2 ∧ (sp - 8 - K ≤ r.1 ∧ r.2 ≤ sp + 0x1b0 ∨ sp + 0x1e8 ≤ r.1 ∧ r.2 ≤ sp + 0x220)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- the stack's array is `0` when empty (entry fact, kept or fresh with `0 < cap`) -/
theorem WC.cap0 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    stCap M st = 0 → stW M st = 0 := by
  intro h0
  by_cases e : stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st
  · rw [e.1]; exact hP.cap0 (by rw [← e.2]; exact h0)
  · have := (h.ain e).2; omega

set_option maxRecDepth 20000 in
/-- `WC` and every destination / live local through the function's own stores -/
theorem WC.own (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory}
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions) (hws : ∀ r ∈ ws, OwnR sp K r) :
    WC R L K g sp st zp zc s.mem M' L1 b1 ℓ ∧
      (∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L1 q c) ∧
      ∀ q l c v, LN R L st zp zc M L1 q l c v → LN R L st zp zc M' L1 q l c v := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hLs : LiveSep L [(sp - 8 - K, sp - 8 + 0x228)] := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  have hwin : ∀ a k, (a + k ≤ sp - 8 - K ∨ sp + 0x220 ≤ a) → Outside a k ws := by
    intro a k ha
    refine outside_of_forall ?_
    intro r hr; have := hws r hr; omega
  have hw : WC R L K g sp st zp zc s.mem M' L1 b1 ℓ := by
    refine h.frame hF hrg (fun a k ho => ?_) (fun a k hin _ => ?_) (hwin _ _ (by omega)) (fun r hr => ?_)
    · refine outside_of_forall fun r hr => ?_
      have := hws r hr
      simp only [WN, outside_append, outside_cons, outside_nil, and_true] at ho
      omega
    · obtain ⟨r, hr, h1, h2⟩ := hin
      have := hLs r hr
      simp only [outside_cons, outside_nil, and_true] at this
      exact hwin _ _ (by omega)
    · right
      have := hws r hr
      exact hout.of_sub (by omega) (by omega)
  have hhd : Outside st 24 ws := hwin st 24 (by omega)
  have e0 : stW M' st = stW M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M' st = stLen M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M' st = stCap M st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have hsb : StackBack R L1 L1 st M M' := ⟨hw.sok, e1, Or.inl ⟨e0, e2⟩⟩
  refine ⟨hw, fun q c hq => hq.back (LiveExt.refl R L1) hF.accessible hsb, fun q l c v hq => ?_⟩
  refine hq.keep (LiveExt.refl R L1) hF.accessible hsb (fun c0 a k h1 h2 => hF.readLE a k (hwin a k ?_))
  have := Loc.win hP hq.1.2.2.1; unfold Apart at this; omega

/-- the stack header is kept by the prologue's frame writes -/
theorem hdr_fw (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FWp sp)) :
    stW M st = stW s.mem st ∧ stLen M st = stLen s.mem st ∧ stCap M st = stCap s.mem st := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  have hhd : Outside st 24 (FWp sp) := by simp only [FWp, outside_cons, outside_nil, and_true]; omega
  exact ⟨hF.readLE _ _ (hhd.of_sub (by omega) (by omega)), hF.readLE _ _ (hhd.of_sub (by omega) (by omega)),
    hF.readLE _ _ (hhd.of_sub (by omega) (by omega))⟩

set_option maxRecDepth 20000 in
/-- **reuse**: the entry `z` array (`0 < cap z`) is a destination after the prologue's frame writes -/
theorem dl_reuse (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FWp sp)) (hc0 : 0 < zc) : DL R L st zp zc M L zp zc := by
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨hH, -, -, hfr⟩, acc, b48, al, -⟩ := hP.zF hc0
  obtain ⟨e0, e1, e2⟩ := hdr_fw hP hF
  refine ⟨hzc, fun _ => ⟨al, hH, by rw [hF.accessible]; exact acc, b48⟩, Or.inl ⟨rfl, rfl, hc0⟩,
    fun _ => ⟨hH, ?_, ?_⟩, fun h => absurd h (by omega)⟩
  · show Apart zp (8 * zc) (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
    rw [e0, e1, e2]; exact hfr
  · intro hin hap; exact (hfresh hH hap hin).symm

set_option maxRecDepth 20000 in
/-- **fresh**: a `makeslice` array `[p, p + r)` of capacity `c` (`8c ≤ r`), allocated at memory `M` (live set `L`,
the stack untouched since the entry) is a destination at `m` (live set `L ++ [(p, p + r)]`) -/
theorem dl_fresh (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M m : Memory} {b1 : Nat}
    (hw : WC R L K g sp st zp zc s.mem M L b1 (stLen s.mem st)) {p rr c : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem M L b1 (stLen s.mem st) m p rr (8 * c)) (hc40 : c < 2 ^ 40)
    (hc0 : 0 < c) : DL R L st zp zc m (L ++ [(p, p + rr)]) p c := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  obtain ⟨hstw, -⟩ := hP.stkF
  have h8c : 8 * c ≤ rr := hA.sz
  have hhd : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    hA.rdH _ _ (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart at hstw ⊢; omega)
  have e0 : stW m st = stW M st := by have := hhd 0 (by omega); simpa using this
  have e1 : stLen m st = stLen M st := hhd 8 (by omega)
  have e2 : stCap m st = stCap M st := hhd 16 (by omega)
  have hin : InRanges p (8 * c) R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  have hap1 : ApartAll p (8 * c) L := fun x hx' => by
    have := hA.rap x hx'; unfold Apart at this ⊢; omega
  have hheld : Held R (L ++ [(p, p + rr)]) p (8 * c) :=
    Or.inl ⟨(p, p + rr), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by simp only; omega⟩
  have hsb : StackBack R L (L ++ [(p, p + rr)]) st M m :=
    ⟨hA.wc.sok, e1, Or.inl ⟨e0, e2⟩⟩
  refine ⟨hc40, fun _ => ⟨hA.al, hheld, Janus.Arm64.Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega), by
      have := hA.b48; omega⟩, Or.inr (Or.inl ⟨hin, hap1⟩), fun _ => ?_, fun h => absurd h (by omega)⟩
  exact ob_fresh (L := L) hw.sok (WC.cap0 hP hw) hsb hin hap1 hheld (fun _ hne => absurd ⟨e0, e2⟩ hne) hc0

end

end FvModexp.Amd64.ExpSlow
