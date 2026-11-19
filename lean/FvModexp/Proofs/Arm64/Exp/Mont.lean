import FvModexp.Proofs.Arm64.Exp.MontLoop
import FvModexp.Proofs.Arm64.Exp.MontAsm

/-!
# `nat.montgomery` (arm64), nat.go:188-218: the roomy summary

For `z` with `cap(z) ≥ 2n` (every call site in the windowed exponentiations: 3-index slices of `buf` with cap `2n`,
and `make(2n)` results), `len(x) = len(y) = len(m) = n > 0`, `z` apart from `x`, `y`, `m`:
`z.montgomery(x, y, m, k, n)` returns `z[:n]` holding `montgomery n X Y M k` (the Nat model, ExpMont.lean), calls only
`memclrNoHeapPointers`, `addMulVVWW` (twice per iteration), `subVV` / `memmove`, allocates nothing.

Frame 192 bytes, 14 argument spill slots above `SP` (`above = 120`); runtime calls need 4096 bytes below the frame:
`stk = 192 + 4096 = 4288`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.MontHyp FvModexp.Exp

namespace FvModexp.Arm64.Mont

/-- the call environment (top's `CallEnv` without `DataLoaded`, which montgomery does not use) -/
@[reducible] def Env (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  GuardOK s stk ∧ StackOK s stk above ∧
    Outside (s.sp.toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - stk) (stk + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L [(s.sp.toNat - stk, s.sp.toNat + above)]

/-- An input nat `p[0:n]`: readable, below `2^48`, held, apart from the stack window. -/
@[reducible] def Input (R : RtInv) (L : List (Nat × Nat)) (s : State) (p n : Nat) : Prop :=
  s.mem.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧
    (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧ Apart p (8 * n) (s.sp.toNat - 4288) (4288 + 120)

def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl mp ml mc k n : BitVec 64) (s : State) : Prop :=
  Env R L s 4288 120 ∧ xl = n ∧ yl = n ∧ ml = n ∧ 0 < n.toNat ∧ 2 * n.toNat ≤ zc.toNat ∧ zc.toNat < 2 ^ 40 ∧
    n.toNat ≤ mc.toNat ∧ mc.toNat < 2 ^ 40 ∧
    s.mem.accessible zp.toNat (8 * zc.toNat) true = true ∧ zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 ∧
    (InRanges zp.toNat (8 * zc.toNat) L ∨ Outside zp.toNat (8 * zc.toNat) R.rt) ∧
    Apart zp.toNat (8 * zc.toNat) (s.sp.toNat - 4288) (4288 + 120) ∧
    Apart ((s.regs 28).toNat + 16) 8 zp.toNat (8 * zc.toNat) ∧
    Input R L s xp.toNat n.toNat ∧ Input R L s yp.toNat n.toNat ∧ Input R L s mp.toNat n.toNat ∧
    Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * n.toNat) ∧ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * n.toNat) ∧
    Apart zp.toNat (8 * zc.toNat) mp.toNat (8 * n.toNat) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [zp.toNat, 16 * n.toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [zp.toNat, zp.toNat + n.toNat * 8, 8 * n.toNat]

def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp yp mp k n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = zp ∧ s'.regs 1 = n ∧ s'.regs 2 = zc ∧
    s'.mem.readLE zp.toNat (8 * n.toNat) =
      montgomery n.toNat (s.mem.readLE xp.toNat (8 * n.toNat)) (s.mem.readLE yp.toNat (8 * n.toNat))
        (s.mem.readLE mp.toNat (8 * n.toNat)) k.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), L' = L ∧ b' = b ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 120)] ++
        [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

set_option hygiene false in
/-- a frame slot of the memory after `clear(z)`: through the memclr frame, then the store chain -/
local macro "slotv" : tactic => `(tactic| (
  rw [slot _ (by omega) (by omega) (by omega) (by omega)]
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  try simp only [Nat.reducePow]
  try omega))

set_option hygiene false in
/-- an input read through the memclr frame and the store chain -/
local macro "inputv" h:term : tactic => `(tactic| (
  rw [FvModexp.Expmc.held_readLE $h F LF (hcs _ _ (by omega) (by omega)) (hz16 _ _ (by omega))]
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens' (impl : List Segment) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hamv : Summary0 (LibMont.program.link impl) (segAddr LibMont.program amvFn) AmvPre AmvQ)
    (hsub : Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc mp ml mc k n : BitVec 64) :
    Ensures (LibMont.program.link impl) (segAddr LibMont.program fn) [zp, zl, zc, xp, xl, xc, yp, yl, yc, mp, ml, mc, k, n]
      (Pre R b L zp zc xp xl yp yl mp ml mc k n) (Post R b L zp zc xp yp mp k n) := by
  janus_ensures_old [FvModexp.Arm64.Mont.Pre, FvModexp.Arm64.Mont.Env, FvModexp.Arm64.Mont.Input, Janus.Spec.GuardOK, Janus.Spec.StackOK]
  intro ret hret s hs hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hwin, hgw, hgrt, hLs⟩, hxl, hyl, hml, hn, hn2, hzc, hmc, hmc', hzacc, hzp,
    hzh, hzw, hgz, ⟨hxacc, hxp, hxh, hxw⟩, ⟨hyacc, hyp, hyh, hyw⟩, ⟨hmacc, hmp, hmh, hmw⟩, hzx, hzy, hzm, hinv,
    hokc, hokm⟩ := hpre
  janus_intro hs
  rw [hxl] at h_x4
  rw [hyl] at h_x7
  rw [hml] at h_x10
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 192 - 4096 ∨ s.sp.toNat - 192 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 192 + 8 ∨ s.sp.toNat - 192 + 8 + 16 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hokc' : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
      [zp.toNat, 8 * (n.toNat + n.toNat)] := by rw [show 8 * (n.toNat + n.toNat) = 16 * n.toNat by omega]; exact hokc
  have hzh16 : InRanges zp.toNat (8 * (n.toNat + n.toNat)) L ∨ Outside zp.toNat (8 * (n.toNat + n.toNat)) R.rt :=
    hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  janus_run until [head] calls [hclr L b]
  rename_i _ _ _ w _ _ F LF IV Zr
  have eA : ∀ a k wr, w.accessible a k wr = s.mem.accessible a k wr := by
    intro a k wr; rw [F.accessible]; simp only [Memory.accessible_writeLE]
  have hcs : ∀ a k, (a + k ≤ s.sp.toNat - 192 - 4096 ∨ s.sp.toNat - 192 - 8 ≤ a) →
      (a + k ≤ s.sp.toNat - 192 + 8 ∨ s.sp.toNat - 192 + 8 + 16 ≤ a) →
      Outside a k [(s.sp.toNat - 192 - 4096, s.sp.toNat - 192 - 8), (s.sp.toNat - 192 + 8, s.sp.toNat - 192 + 8 + 16)] := by
    intro a k h1 h2; simp only [outside_cons, outside_nil, and_true]; omega
  have hz16 : ∀ a k, (a + k ≤ zp.toNat ∨ zp.toNat + 8 * (n.toNat + n.toNat) ≤ a) →
      Outside a k [(zp.toNat, zp.toNat + 8 * (n.toNat + n.toNat))] := by
    intro a k h; simp only [outside_cons, outside_nil, and_true]; omega
  have hretlt := hret.user
  have hX : w.readLE xp.toNat (8 * n.toNat) = s.mem.readLE xp.toNat (8 * n.toNat) := by
    have u1 := hxw; have u2 := hzx; unfold Apart at u1 u2; inputv hxh
  have hY : w.readLE yp.toNat (8 * n.toNat) = s.mem.readLE yp.toNat (8 * n.toNat) := by
    have u1 := hyw; have u2 := hzy; unfold Apart at u1 u2; inputv hyh
  have hM : w.readLE mp.toNat (8 * n.toNat) = s.mem.readLE mp.toNat (8 * n.toNat) := by
    have u1 := hmw; have u2 := hzm; unfold Apart at u1 u2; inputv hmh
  have hG : w.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    have u1 := hgw; have u2 := hgz; unfold Apart at u1 u2
    rw [F.readLE _ _ (by simp only [outside_append]; exact ⟨⟨hgrt, hcs _ _ (by omega) (by omega)⟩, hz16 _ _ (by omega)⟩)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hzw' := hzw
  unfold Apart at hzw'
  have slot : ∀ a, s.sp.toNat - 4288 ≤ a → a + 8 ≤ s.sp.toNat + 120 →
      (a + 8 ≤ s.sp.toNat - 192 - 4096 ∨ s.sp.toNat - 192 - 8 ≤ a) →
      (a + 8 ≤ s.sp.toNat - 192 + 8 ∨ s.sp.toNat - 192 + 8 + 16 ≤ a) → w.readLE a 8 = _ := fun a h1 h2 h3 h4 =>
    FvModexp.Expmc.slot_read F hwin h1 (by omega) (hcs a 8 h3 h4) (hz16 a 8 (by omega))
  refine Reaches.mono (MontLoop.loop (impl := impl) (R := R) (hamv := hamv) (hsub := hsub) (hmv := hmv) (ret := ret)
    (hret := hret) (s := s) (L := L) (b := b) (sp := s.sp.toNat - 192) (zp := zp.toNat) (cap := zc.toNat)
    (xp := xp.toNat) (xc := xc.toNat) (yp := yp.toNat) (mp := mp.toNat) (mc := mc.toNat) (k := k.toNat) (n := n.toNat)
    (M0 := w) (hsps := by omega) (hal := by omega) (hsp4 := by omega) (hsp48 := by omega)
    (hacc := by rw [eA, show s.sp.toNat - 192 - 4096 = s.sp.toNat - 4288 by omega, show 4096 + 312 = 4288 + 120 from rfl]; exact hw)
    (hn := hn) (hn2 := hn2) (hcap := hzc) (hxc := xc.isLt) (hmc := hmc) (hmc' := hmc') (hk := k.isLt)
    (hzp := hzp) (hzacc := by rw [eA]; exact hzacc) (hxacc := by rw [eA]; exact hxacc) (hxp := hxp)
    (hyacc := by rw [eA]; exact hyacc) (hyp := hyp) (hmacc := by rw [eA]; exact hmacc) (hmp := hmp)
    (hzx := hzx) (hzy := hzy) (hzm := hzm)
    (hzs := by unfold Apart; omega) (hxs := by have u := hxw; unfold Apart at u ⊢; omega) (hys := by have u := hyw; unfold Apart at u ⊢; omega)
    (hms := by have u := hmw; unfold Apart at u ⊢; omega)
    (r104 := by slotv) (r112 := by slotv) (r168 := by slotv) (r224 := by slotv) (r232 := by slotv)
    (r240 := by slotv) (r248 := by slotv) (r272 := by slotv) (r280 := by slotv) (r288 := by slotv)
    (r296 := by slotv) (r304 := by slotv) (hret0 := by slotv) (hfp := by slotv)
    (hg := hg1) (hgacc := by rw [eA]; exact hg2) (hgs := by have u := hgw; unfold Apart at u ⊢; omega) (hgz := hgz)
    (hguard := by rw [hG]; omega) (hgrt := hgrt)
    (hwin := by rw [show 4096 + 312 = 4288 + 120 by rfl, show s.sp.toNat - 192 - 4096 = s.sp.toNat - 4288 by omega]; exact hwin)
    (hzh := hzh) (hLs := fun r hr => by
      have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)
    (hinv := IV) (hok := hokm) n.toNat _ 0 0 w (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (MemFrame.refl _ _) ?_ rfl) ?_
  all_goals first
    | rfl
    | exact FvModexp.Expmc.sp_sub _ _ (by omega) (by omega)
    | (janus_simp [FvModexp.Expmc.bv_ofNat_toNat]; done)
    | (janus_simp [FvModexp.Expmc.bv_ofNat_toNat, Nat.two_mul]; done)
    | skip
  · rw [show 8 * (2 * n.toNat) = 8 * (n.toNat + n.toNat) by omega, FvModexp.Expmc.readLE_zeroed Zr]; rfl
  · intro o ho
    cases o with
    | stub _ _ _ => exact ho.elim
    | returned s' =>
      simp only [isReturn_returned] at ho ⊢
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, ev, ei, ef, el⟩ := ho
      have hF0 : MemFrame s.mem w (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 120),
          (zp.toNat, zp.toNat + 8 * (n.toNat + n.toNat))]) := by janus_frame
      have hL0 : LiveFrame s.mem w L [(zp.toNat, zp.toNat + 8 * (n.toNat + n.toNat))] := by
        refine ⟨fun a k hin hout => ?_⟩
        rw [LF.readLE a k hin hout]
        obtain ⟨r, hr, h1, h2⟩ := hin
        have := hLs r hr
        simp only [outside_cons, outside_nil, and_true] at this
        simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
      refine ⟨⟨e1, e3, e4, e2⟩, by rw [e5, FvModexp.Expmc.bv_ofNat_toNat], by rw [e6, FvModexp.Expmc.bv_ofNat_toNat],
        by rw [e7, FvModexp.Expmc.bv_ofNat_toNat], by rw [ev, hX, hY, hM], L, b, rfl, rfl, ei, ?_, ?_⟩
      · refine hF0.trans ef (fun a k hk => ?_)
        simp only [outside_append, outside_cons, outside_nil, and_true] at hk ⊢
        exact ⟨⟨hk.1.1, by omega, by omega, by omega⟩, ⟨hk.1.1, by omega, by omega, by omega⟩⟩
      · refine FvModexp.Expmc.liveFrame_widen (hL0.trans (FvModexp.Expmc.liveFrame_widen el ?_) (fun _ _ h => h)) ?_
        · intro a k h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
        · intro a k h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

end FvModexp.Arm64.Mont

namespace FvModexp.Arm64.Mont

open Janus.Contracts.EqHashModel

/-- `ens'` in the project's statement shape (docs/history/CONVENTIONS-v2.md §3, agent top): the program is the restricted Run
program of `names`, the runtime contracts are about `Extracted.program.ofImpl impl`, the only premise on `impl` is
`ImplApart`. The asm kernels `addMulVVWW`/`subVV` are agent asm's verified summaries (`MontAsm`): no premise. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc mp ml mc k n : BitVec 64) :
    Ensures ((Extracted.program.onlySegments LibMont.names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc, mp, ml, mc, k, n]
      (Pre R b L zp zc xp xl yp yl mp ml mc k n) (Post R b L zp zc xp yp mp k n) := by
  have hc := codeIn_ofImpl_restrict_of_apart hap LibMont.names
  have e3 : segAddr Extracted.program fn = segAddr LibMont.program fn := by decide
  rw [← LibMont.eq_only] at hc ⊢
  rw [e3]
  exact ens' impl R (MemclrNoHeapPointersLive.of_codeIn hc hclr) (MemmoveLive.of_codeIn hc hmv)
    (MontAsm.amv_sum impl) (MontAsm.sub_sum impl) b L zp zl zc xp xl xc yp yl yc mp ml mc k n

end FvModexp.Arm64.Mont
