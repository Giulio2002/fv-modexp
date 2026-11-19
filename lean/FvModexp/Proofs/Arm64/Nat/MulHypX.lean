import FvModexp.Proofs.Arm64.Nat.NatMul
import FvModexp.Proofs.Arm64.Nat.SqrMulX
import FvModexp.Proofs.Arm64.Exp.RdIn0
import FvModexp.Proofs.Arm64.Nat.MulPre0

set_option autoImplicit false

/-!
# `nat.mul` (arm64) in the callers' premise forms (owner divmc)

* `EvenHyp.MulPre0` / `MulHypX0`: infra's `MulPre` / divmc's `MulHypX` with BOTH operands empty-tolerant (`RdIn0`;
  coordinator decision on "[infra s30] FINDING": `nat.expNN` can return a nil `nat`, which `expNNEven` passes to `mul`).
  `MulPre.to0` / `MulHypX0.toX` give the old forms back.
* `EvenHyp.ExactE` / `MulHypXE0`: `MulHypX0` whose post also carries the exact-write clause on the result registers
  (= asm's `DivRec.ExactR`, see `NatMulXE` for the `DivRec.MulHypXE` form).
* `NatMul.hypX0 : MulHypX0 impl R NatMul.names mulWX 88 mulC`, `NatMul.hypX : MulHypX …`, `NatMul.hypXE0`, from
  `NatMul.ens` at the window `W = mulWX` (every length `≤ 2^12` fits): `x_pre` (pre → `MPre`), `x_post`
  (`MPost` → `MulPostL ∧ Reuse`), `x_exact` (`MPost` → `ExactE`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.ExpHyp (RdIn RdIn0 WrOut RtPost NatOF stWs)

def MulHypX0 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre0 R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat)
      (fun s s' => MulPostL R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zc.toNat st.toNat
        x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

theorem MulHypX0.toX {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat → Nat} (h : MulHypX0 impl R ns stk above cost) : MulHypX impl R ns stk above cost :=
  fun b L z zl zc st x xl xc y yl yc =>
    (h b L z zl zc st x xl xc y yl yc).mono_ret (fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.to0, h2, h3, h4⟩) (fun _ _ _ _ hq => hq)

/-- `MulHypX0` with the exact-write clause in the post -/
def MulHypXE0 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat → Nat) :
    Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre0 R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat)
      (fun s s' => MulPostL R b (cost (stLen s.mem st.toNat) xl.toNat yl.toNat) L stk above z.toNat zc.toNat st.toNat
        x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        ExactE R L (winA s stk above) (xl.toNat + yl.toNat) z.toNat zc.toNat st.toNat x.toNat xc.toNat y.toNat
          yc.toNat (natVal s.mem x.toNat xl.toNat * natVal s.mem y.toNat yl.toNat) s s')

end FvModexp.Arm64.EvenHyp

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0)


set_option maxRecDepth 20000 in
theorem x_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat} {s : State}
    (h : MulPre0 R b (mulC (stLen s.mem st) xl yl) L mulWX 88 zp zl zc st x xl y yl s)
    (hcx : CapIn R L x xl xc) (hcy : CapIn R L y yl yc)
    (hx : MulX R L s mulWX 88 st zp zc x xl xc y yl yc) : MPre R b L mulWX zp zc st x xl xc y yl yc s := by
  obtain ⟨hce, hsv, hglb, -, ⟨hz40, hzl, hzw⟩, ⟨hxl40, hxr⟩, ⟨hyl40, hyr⟩, hx12, hy12, hzx, hzy,
    ⟨hsok, hstw, hstg, hsta⟩, hlen, hza, hxa, hya, hcost, hinv⟩ := h
  obtain ⟨hxc, hxc40, hxh, hx48⟩ := hcx
  obtain ⟨hyc, hyc40, hyh, hy48⟩ := hcy
  obtain ⟨⟨hst0, hswb, hfh, hfw, hfg, hsf, hsgA, hfgA⟩, hzo, hzxc, hzyc, hzop, hxop, hyop⟩ := hx
  have hro : RoOut R := hce.2.2.2.2.2.2.2
  refine ⟨hce, mulW_le_X hx12 hy12, hsv, hglb, wordT_rt' hro,
    ⟨⟨hxc, hxc40, hx12, fun h0 => (hxr h0).2.1, fun _ => ⟨hxh, hx48⟩,
      fun h0 => ⟨(hxr h0).2.2.2.2, (hxa (by omega)).1.symm, (hxop (by omega)).1, (hxop (by omega)).2⟩⟩,
     ⟨hyc, hyc40, hy12, fun h0 => (hyr h0).2.1, fun _ => ⟨hyh, hy48⟩,
      fun h0 => ⟨(hyr h0).2.2.2.2, (hya (by omega)).1.symm, (hyop (by omega)).1, (hyop (by omega)).2⟩⟩,
     ⟨hz40, hzl, hzo, fun h0 => ⟨(hzw h0).2, (hza (by omega)).1.symm, (hzop (by omega)).1, (hzop (by omega)).2⟩,
      ?_, ?_⟩, hlen⟩,
    ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩, hcost, hinv⟩
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
theorem x_post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc st x xl xc y yl yc : Nat} {s s' : State}
    (h : MPost R b L mulWX zp zc st x xl xc y yl yc s s') :
    MulPostL R b (mulC (stLen s.mem st) xl yl) L mulWX 88 zp zc st x xl y yl s s' ∧
      Reuse (xl + yl) zp zc [(x, xc), (y, yc)] s' := by
  obtain ⟨p', l', c', r0, r1, r2, hv, hn, hlc, -, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex, hsb, hF,
    hLF⟩ := h
  refine ⟨⟨p', l', c', r0, r1, r2, L', b', ⟨hv, hn, hlc, hc40, hlive, hkind⟩, ⟨hext, hbud, hinv⟩, hsb, hfa, hF, hLF⟩,
    fun hn2 hne => ?_⟩
  obtain ⟨e1, e2, -⟩ := hex hn2 (hne _ List.mem_cons_self) (hne _ (List.mem_cons_of_mem _ List.mem_cons_self))
  subst e1 e2
  exact ⟨r0, r2⟩

set_option maxRecDepth 20000 in
theorem x_exact {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc st x xl xc y yl yc : Nat} {s s' : State}
    (h : MPost R b L mulWX zp zc st x xl xc y yl yc s s') :
    ExactE R L (winA s mulWX 88) (xl + yl) zp zc st x xc y yc (natVal s.mem x xl * natVal s.mem y yl) s s' := by
  obtain ⟨p', l', c', r0, -, r2, -, -, -, -, -, L', b', -, -, -, -, -, -, hex, -⟩ := h
  intro h1 h2 h3
  obtain ⟨e1, e2, hv, hF, hLF⟩ := hex h1 h2 h3
  subst e1 e2
  exact ⟨r0, r2, hv, hF, hLF⟩

/-- **`nat.mul`** (arm64) in the `MulHypX0` premise form (empty-tolerant operands), window `mulWX`, `above = 88`,
cost `mulC` -/
theorem hypX0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypX0 impl R names mulWX 88 mulC := fun b L z zl zc st x xl xc y yl yc =>
  (ens impl hap R hmk hgr hmc hmv hwb b L mulWX z zl zc st x xl xc y yl yc).mono_ret
    (fun _ ⟨h1, h2, h3, h4⟩ => x_pre h1 h2 h3 h4) (fun _ _ _ _ hq => x_post hq)

/-- **`nat.mul`** (arm64) in the `MulHypX` premise form (= `hypX0.toX`) -/
theorem hypX (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypX impl R names mulWX 88 mulC :=
  (hypX0 impl hap R hmk hgr hmc hmv hwb).toX

/-- **`nat.mul`** (arm64) with the exact-write clause (`MulHypXE0`) -/
theorem hypXE0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypXE0 impl R names mulWX 88 mulC := fun b L z zl zc st x xl xc y yl yc =>
  (ens impl hap R hmk hgr hmc hmv hwb b L mulWX z zl zc st x xl xc y yl yc).mono_ret
    (fun _ ⟨h1, h2, h3, h4⟩ => x_pre h1 h2 h3 h4) (fun _ _ _ _ hq => ⟨(x_post hq).1, x_exact hq⟩)

end FvModexp.Arm64.NatMul
