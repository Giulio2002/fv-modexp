import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.NatQ.DrsFV

/-! (Q-form copy of Arm64/Nat/DrsFG.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block: the state after `addTo(z, qhat.norm())` and the post (pure)

* `GF`: the state at `0x1bacdc` (after `addTo(z, qhat.norm())`, natdiv.go:891): the environment, the fixed slots and
  the results `z = (finalBlock …).1`, `u[:u1] = (finalBlock …).2` (`Mdl.finalBlock`, DivRecFin).
* `finWF`: what the rest writes (the defer bit, the deferred closure's frame, the stack header's `len` word).
* **`postF`**: from `GF`, a final memory that differs only in `finWF` and has `len(stk.w)` back at its entry value
  (the deferred `stk.restore(stk.save())`), `DrsPostW` holds: `z = U / V`, `u = U mod V`, the budget, the stack
  (`StackBack`), the frames.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

/-- **the end of the final block** (before the deferred `stk.restore`) -/
structure GF (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) : Prop where
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s + StackNat.rnd (3 * c.vl))
  sl : Sl c s S.mem
  zk : Asm.limbs S.mem c.qp c.ql = (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).1
  uk : Asm.limbs S.mem c.up c.u1 = (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).2
  utl : S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  li : c.LI s j Z U
  jB : j ≤ c.vl / 2
  bud : c.lo s + stkR c.Hq S.mem c.st ≤ bk

/-- the writes after `GF`: the defer bit (`SP'+103`), the closure's frame (`SP'-24 … SP'-8`), `len(stk.w)` -/
@[reducible] def finWF (s : State) (st : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - 297, s.sp.toNat - 296), (s.sp.toNat - 424, s.sp.toNat - 408), (st + 8, st + 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the post of the big path** (pure) -/
theorem postF {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {S : State} {j : Nat}
    {Z U : List Nat} (hG : GF R c s Lk bk S j Z U) {Mf : Memory} (hW : MemFrame S.mem Mf (finWF s c.st))
    (hlen : Mf.readLE (c.st + 8) 8 = stLen s.mem c.st) (s' : State) (hm : s'.mem = Mf) :
    DrsPostW R c.b c.L c.Hq (drsCQ c.ul c.vl) c.W c.qp c.ql c.st c.up c.ul c.vp c.vl s s' := by
  subst hm
  have hcr := hG.cr
  have hev := hG.ev
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, hql9⟩, -, -, -, ⟨hqa, hq48, hqh, hqw, hqg⟩,
    ⟨hua, hu48, huh, huw, hug⟩, -, hqu, -, -, hsti, -, ⟨hqs, -⟩, ⟨hus, -⟩, -⟩ := hcr.pre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, hLs, -⟩ := hce'
  have hWg := drsW_ge c.vl; have hW' := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hst := hsti.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hqw huw hst
  have rdf : ∀ a n, (a + n ≤ s.sp.toNat - c.W ∨ s.sp.toNat + 96 ≤ a) → (a + n ≤ c.st + 8 ∨ c.st + 16 ≤ a) →
      s'.mem.readLE a n = S.mem.readLE a n := fun a n h1 h2 =>
    hW.readLE a n (by simp only [finWF, outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n w, s'.mem.accessible a n w = S.mem.accessible a n w := fun a n w => hW.accessible a n w
  have hfs := fstep hcr hG.li hG.jB
  have hVv : Mdl.val (c.V s) = natVal s.mem c.vp c.vl := Asm.val_limbs _ _ _
  have hU := hcr.hU
  -- `u`'s tail (beyond `u1`) is zero
  have e1 : ∀ M : Memory, M.readLE c.up (8 * c.ul) =
      M.readLE c.up (8 * c.u1) + 256 ^ (8 * c.u1) * M.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) := fun M => by
    rw [← Memory.readLE_add]; congr 1; omega
  have htl0 : s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = 0 := by
    have h := e1 s.mem
    have h' : s.mem.readLE c.up (8 * c.u1) = s.mem.readLE c.up (8 * c.ul) := hU
    have hp : 0 < 256 ^ (8 * c.u1) := Nat.pow_pos (by decide)
    rw [h'] at h
    have : 256 ^ (8 * c.u1) * s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = 0 := by omega
    rcases Nat.mul_eq_zero.1 this with h0 | h0
    · omega
    · exact h0
  have eW : stW s'.mem c.st = stW S.mem c.st := rdf _ _ (by omega) (by omega)
  have eC : stCap s'.mem c.st = stCap S.mem c.st := rdf _ _ (by omega) (by omega)
  have eL : stLen s'.mem c.st = stLen s.mem c.st := hlen
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hev.sok
  have hfl := hG.fp.len
  refine ⟨?q, ?u, Lk, bk, ⟨hext, ?bud, ?inv⟩, ⟨⟨?stok, eL, ?arr⟩, hev.sarrL.congr eW eC fun _ h => h⟩, ?fr, ?lf⟩
  case q =>
    have e : natVal s'.mem c.qp c.ql = natVal S.mem c.qp c.ql := rdf _ _ (by omega) (by unfold Apart at hqs; omega)
    have e2 : natVal S.mem c.qp c.ql = Mdl.val (Asm.limbs S.mem c.qp c.ql) := (Asm.val_limbs _ _ _).symm
    rw [e, e2, hG.zk, hfs.2.2.2.2.1, hVv, hU]
  case u =>
    have e : natVal s'.mem c.up c.ul = natVal S.mem c.up c.ul := rdf _ _ (by omega) (by unfold Apart at hus; omega)
    rw [e]
    show S.mem.readLE c.up (8 * c.ul) = _
    rw [e1 S.mem, hG.utl, htl0, Nat.mul_zero, Nat.add_zero]
    have e2 : S.mem.readLE c.up (8 * c.u1) = Mdl.val (Asm.limbs S.mem c.up c.u1) := (Asm.val_limbs _ _ _).symm
    rw [e2, hG.uk, hfs.2.2.2.2.2.1, hVv, hU]
  case bud => have := hG.bud; unfold Cx.lo at this; exact bud_cap eC this
  case inv =>
    refine RtInv.inv_frame' hW (fun r hr => ?_) hev.inv
    simp only [finWF, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · simp only [show c.st + 16 - (c.st + 8) = 8 by omega]
      rcases h2.sub (a := c.st + 8) (n := 8) (by omega) (by omega) with h | h
      · right; exact h
      · left; exact h
  case stok =>
    unfold StkOK
    rw [eW, eC]
    refine ⟨h1, h2, by rw [hacc]; exact h3, h4, ?_, ?_, h7⟩
    · intro hc; obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, q2, by rw [hacc]; exact q3, q4⟩
    · show s'.mem.readLE (c.st + 8) 8 ≤ _
      rw [hlen]
      have : stLen S.mem c.st ≤ stCap S.mem c.st := h6
      simp only [Cx.l1] at hfl
      omega
  case arr =>
    rw [eW, eC]
    rcases hev.sarr with h | h
    · exact Or.inl h
    · exact Or.inr h
  case fr =>
    refine hev.fr.trans hW fun a n ho => ⟨?_, ?_⟩
    · simp only [Cx.ws, outside_append] at ho ⊢
      exact ⟨ho.1.1, ho.1.2, ho.2⟩
    · simp only [outside_append, winA, stkWs, outside_cons, outside_nil, and_true] at ho
      simp only [finWF, outside_cons, outside_nil, and_true]
      omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [hW.readLE a n ?_]
    · exact hev.lf.readLE a n hin ho
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    simp only [win, outside_append, stkWs, outside_cons, outside_nil, and_true] at this ho
    simp only [finWF, outside_cons, outside_nil, and_true]
    omega

end FvModexp.Arm64.Q.DivRec
