import FvModexp.Proofs.Arm64.NatQ.NatMul
import FvModexp.Proofs.Arm64.NatQ.MulHypQE
import FvModexp.Proofs.Arm64.Exp.RdIn0

set_option autoImplicit false

/-!
# `nat.mul` (arm64) as `divRecursiveStep` uses it, Q-form: `Q.DivRec.mulHyp : Q.DivRec.MulHypQE … NatMul.names mulWX 88 mulCQ`

Directly from divmc's `Q.NatMul.ens` (NatQ/NatMul.lean) — the same argument as divmc's `Q.NatMul.hypQE`
(adapted from NatQ/MulHypQ.lean `q_pre`/`q_post`/`q_exact`, owner divmc), but WITHOUT importing the old-form
`Nat/MulHypX.lean` (whose closure is the whole old `nat.mul` chain): the drs/div/rem rows import this module instead,
so they do not compile the old chain (asm s42, row-time trim). Statement = `Q.DivRec.MulHypQE` (asm, NatQ/MulHypQE.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.DivRec

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0)
open FvModexp.Arm64.Q.NatMul (MPre MPost)

set_option maxRecDepth 20000 in
theorem wordT_rtD {R : RtInv} (hro : RoOut R) : Outside NatAdd.wordT 16 R.rt :=
  RoOut.out' hro 1 (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem mulD_pre {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat} {s : State}
    (h : MulPre R b (mulCQ xl yl + stkR H s.mem st) L mulWX 88 zp zl zc st x xl y yl s)
    (hcx : CapIn R L x xl xc) (hcy : CapIn R L y yl yc)
    (hx : MulX R L s mulWX 88 st zp zc x xl xc y yl yc) (hH : stLen s.mem st + 4 * (xl + yl) + 64 ≤ H) :
    MPre R b H L mulWX zp zc st x xl xc y yl yc s := by
  obtain ⟨hce, hsv, hglb, -, ⟨hz40, hzl, hzw⟩, hxR, hyR, hx12, hy12, hzx, hzy,
    ⟨hsok, hstw, hstg, hsta⟩, hlen, hza, hxa, hya, hcost, hinv⟩ := h
  obtain ⟨hxl40, hxr⟩ := hxR.toRdIn0
  obtain ⟨hyl40, hyr⟩ := hyR.toRdIn0
  obtain ⟨hxc, hxc40, hxh, hx48⟩ := hcx
  obtain ⟨hyc, hyc40, hyh, hy48⟩ := hcy
  obtain ⟨⟨hst0, hswb, hfh, hfw, hfg, hsf, hsgA, hfgA⟩, hzo, hzxc, hzyc, hzop, hxop, hyop⟩ := hx
  have hro : RoOut R := hce.2.2.2.2.2.2.2
  refine ⟨hce, mulW_le_X hx12 hy12, hsv, hglb, wordT_rtD hro,
    ⟨⟨hxc, hxc40, hx12, fun h0 => (hxr h0).2.1, fun _ => ⟨hxh, hx48⟩,
      fun h0 => ⟨(hxr h0).2.2.2.2, (hxa (by omega)).1.symm, (hxop (by omega)).1, (hxop (by omega)).2⟩⟩,
     ⟨hyc, hyc40, hy12, fun h0 => (hyr h0).2.1, fun _ => ⟨hyh, hy48⟩,
      fun h0 => ⟨(hyr h0).2.2.2.2, (hya (by omega)).1.symm, (hyop (by omega)).1, (hyop (by omega)).2⟩⟩,
     ⟨hz40, hzl, hzo, fun h0 => ⟨(hzw h0).2, (hza (by omega)).1.symm, (hzop (by omega)).1, (hzop (by omega)).2⟩,
      ?_, ?_⟩, hlen⟩,
    ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩, ⟨hH, hcost⟩, hinv⟩
  · by_cases he : zp = x
    · exact Or.inl ⟨he, hzxc he⟩
    · rcases hzx with h1 | h1
      · exact absurd h1 he
      · exact Or.inr h1
  · by_cases he : zp = y
    · exact Or.inl ⟨he, hzyc he⟩
    · rcases hzy with h1 | h1
      · exact absurd h1 he
      · exact Or.inr h1

set_option maxRecDepth 20000 in
theorem mulD_post {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zc st x xl xc y yl yc : Nat} {s s' : State}
    (h : MPost R b H L mulWX zp zc st x xl xc y yl yc s s') :
    MulPostQ R b (mulCQ xl yl + stkR H s.mem st) (stkR H s'.mem st) L mulWX 88 zp zc st x xl y yl s s' ∧
      ExactR R L (winA s mulWX 88) (xl + yl) zp zc st x xc y yc (natVal s.mem x xl * natVal s.mem y yl) s s' := by
  obtain ⟨p', l', c', r0, r1, r2, hv, hn, hlc, -, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex, hsb, hF,
    hLF⟩ := h
  refine ⟨⟨p', l', c', r0, r1, r2, L', b', ⟨hv, hn, hlc, hc40, hlive, hkind⟩, ⟨hext, hbud, hinv⟩, hsb, hfa, hF, hLF⟩,
    fun h1 h2 h3 => ?_⟩
  obtain ⟨e1, e2, hv', hF', hLF'⟩ := hex h1 h2 h3
  subst e1 e2
  exact ⟨r0, r2, hv', hF', hLF'⟩

/-- **`nat.mul`** (arm64) as `divRecursiveStep` uses it (`Q.DivRec.MulHypQE`): window `mulWX`, `above = 88`, cost
`mulCQ`, from divmc's `Q.NatMul.ens` -/
theorem mulHyp (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypQE impl R NatMul.names mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
  (Q.NatMul.ens impl hap R hmk hgr hmc hmv hwb H b L mulWX z zl zc st x xl xc y yl yc).mono_ret
    (fun _ ⟨h1, h2, h3, h4, h5⟩ => mulD_pre h1 h2 h3 h4 h5) (fun _ _ _ _ hq => mulD_post hq)

end FvModexp.Arm64.Q.DivRec
