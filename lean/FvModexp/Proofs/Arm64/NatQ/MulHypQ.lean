import FvModexp.Proofs.Arm64.NatQ.NatMul
import FvModexp.Proofs.Arm64.NatQ.SqrMulQ
import FvModexp.Proofs.Arm64.Nat.MulHypX

set_option autoImplicit false

/-!
# `nat.mul` (arm64) in the Q-form premises (TIGHT COSTS; owner divmc; the twins of Nat/MulHypX.lean)

* `EvenHyp.MulHypQ0`: `MulHypQ` (NatQ/SqrMulQ.lean) with both operands empty-tolerant (`MulPre0`); `MulHypQ0.toQ`.
* `EvenHyp.MulHypQE0` / `MulHypQE`: the same with the exact-write clause `ExactE` (= asm's `DivRec.ExactR`, same body)
  in the post; `MulHypQE0.toQE`.
* `Q.NatMul.hypQ0 : MulHypQ0 impl R names mulWX 88 mulCQ`, `hypQ`, `hypQE0`, `hypQE`, from `Q.NatMul.ens` at the
  window `mulWX` (`q_pre`, `q_post`, `q_exact`).
Pre: the interface cost is `mulCQ xl yl + stkR H s.mem st` plus the level twin `stLen s.mem st + 4·(xl + yl) + 64 ≤ H`;
post: `RtPostQ … (stkR H s'.mem st)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

open FvModexp.Arm64.ExpHyp (RdIn RdIn0)

/-- **the Q-form `nat.mul` premise, empty-tolerant operands** -/
def MulHypQ0 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre0 R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat ∧
        stLen s.mem st.toNat + 4 * (xl.toNat + yl.toNat) + 64 ≤ H)
      (fun s s' => MulPostQ R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        Reuse (xl.toNat + yl.toNat) z.toNat zc.toNat [(x.toNat, xc.toNat), (y.toNat, yc.toNat)] s')

theorem MulHypQ0.toQ {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat} (h : MulHypQ0 impl R ns stk above cost) : MulHypQ impl R ns stk above cost :=
  fun H b L z zl zc st x xl xc y yl yc =>
    (h H b L z zl zc st x xl xc y yl yc).mono (fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.to0, h2, h3, h4, h5⟩)
      (fun _ _ _ hq => hq)

/-- **`MulHypQ0` with the exact-write clause** in the post -/
def MulHypQE0 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre0 R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat ∧
        stLen s.mem st.toNat + 4 * (xl.toNat + yl.toNat) + 64 ≤ H)
      (fun s s' => MulPostQ R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        ExactE R L (winA s stk above) (xl.toNat + yl.toNat) z.toNat zc.toNat st.toNat x.toNat xc.toNat y.toNat
          yc.toNat (natVal s.mem x.toNat xl.toNat * natVal s.mem y.toNat yl.toNat) s s')

/-- `MulHypQE0` with non-empty-tolerant operands (`MulPre`; asm's `DivRec.MulHypXE` shape) -/
def MulHypQE (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) (cost : Nat → Nat → Nat) :
    Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc y yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnMul)
      [z, zl, zc, st, x, xl, xc, y, yl, yc]
      (fun s => MulPre R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) L stk above z.toNat zl.toNat zc.toNat
        st.toNat x.toNat xl.toNat y.toNat yl.toNat s ∧ CapIn R L x.toNat xl.toNat xc.toNat ∧
        CapIn R L y.toNat yl.toNat yc.toNat ∧
        MulX R L s stk above st.toNat z.toNat zc.toNat x.toNat xl.toNat xc.toNat y.toNat yl.toNat yc.toNat ∧
        stLen s.mem st.toNat + 4 * (xl.toNat + yl.toNat) + 64 ≤ H)
      (fun s s' => MulPostQ R b (cost xl.toNat yl.toNat + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) L stk above
        z.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat s s' ∧
        ExactE R L (winA s stk above) (xl.toNat + yl.toNat) z.toNat zc.toNat st.toNat x.toNat xc.toNat y.toNat
          yc.toNat (natVal s.mem x.toNat xl.toNat * natVal s.mem y.toNat yl.toNat) s s')

theorem MulHypQE0.toQE {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {cost : Nat → Nat → Nat} (h : MulHypQE0 impl R ns stk above cost) : MulHypQE impl R ns stk above cost :=
  fun H b L z zl zc st x xl xc y yl yc =>
    (h H b L z zl zc st x xl xc y yl yc).mono (fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.to0, h2, h3, h4, h5⟩)
      (fun _ _ _ hq => hq)

end FvModexp.Arm64.EvenHyp

namespace FvModexp.Arm64.Q.NatMul

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0)
open FvModexp.Arm64.NatMul (wordT_rt')

set_option maxRecDepth 20000 in
theorem q_pre {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat} {s : State}
    (h : MulPre0 R b (mulCQ xl yl + stkR H s.mem st) L mulWX 88 zp zl zc st x xl y yl s)
    (hcx : CapIn R L x xl xc) (hcy : CapIn R L y yl yc)
    (hx : MulX R L s mulWX 88 st zp zc x xl xc y yl yc) (hH : stLen s.mem st + 4 * (xl + yl) + 64 ≤ H) :
    MPre R b H L mulWX zp zc st x xl xc y yl yc s := by
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
theorem q_post {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zc st x xl xc y yl yc : Nat} {s s' : State}
    (h : MPost R b H L mulWX zp zc st x xl xc y yl yc s s') :
    MulPostQ R b (mulCQ xl yl + stkR H s.mem st) (stkR H s'.mem st) L mulWX 88 zp zc st x xl y yl s s' ∧
      Reuse (xl + yl) zp zc [(x, xc), (y, yc)] s' := by
  obtain ⟨p', l', c', r0, r1, r2, hv, hn, hlc, -, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex, hsb, hF,
    hLF⟩ := h
  refine ⟨⟨p', l', c', r0, r1, r2, L', b', ⟨hv, hn, hlc, hc40, hlive, hkind⟩, ⟨hext, hbud, hinv⟩, hsb, hfa, hF, hLF⟩,
    fun hn2 hne => ?_⟩
  obtain ⟨e1, e2, -⟩ := hex hn2 (hne _ List.mem_cons_self) (hne _ (List.mem_cons_of_mem _ List.mem_cons_self))
  subst e1 e2
  exact ⟨r0, r2⟩

set_option maxRecDepth 20000 in
theorem q_exact {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zc st x xl xc y yl yc : Nat} {s s' : State}
    (h : MPost R b H L mulWX zp zc st x xl xc y yl yc s s') :
    ExactE R L (winA s mulWX 88) (xl + yl) zp zc st x xc y yc (natVal s.mem x xl * natVal s.mem y yl) s s' := by
  obtain ⟨p', l', c', r0, -, r2, -, -, -, -, -, L', b', -, -, -, -, -, -, hex, -⟩ := h
  intro h1 h2 h3
  obtain ⟨e1, e2, hv, hF, hLF⟩ := hex h1 h2 h3
  subst e1 e2
  exact ⟨r0, r2, hv, hF, hLF⟩

/-- **`nat.mul`** (arm64) in the Q-form premise `MulHypQ0` (empty-tolerant operands), window `mulWX`, `above = 88`,
cost `mulCQ` -/
theorem hypQ0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypQ0 impl R names mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
  (ens impl hap R hmk hgr hmc hmv hwb H b L mulWX z zl zc st x xl xc y yl yc).mono
    (fun _ ⟨h1, h2, h3, h4, h5⟩ => q_pre h1 h2 h3 h4 h5) (fun _ _ _ hq => q_post hq)

/-- **`nat.mul`** (arm64) in the Q-form premise `MulHypQ` (= `hypQ0.toQ`) -/
theorem hypQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypQ impl R names mulWX 88 mulCQ :=
  (hypQ0 impl hap R hmk hgr hmc hmv hwb).toQ

/-- **`nat.mul`** (arm64) with the exact-write clause (`MulHypQE0`) -/
theorem hypQE0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypQE0 impl R names mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
  (ens impl hap R hmk hgr hmc hmv hwb H b L mulWX z zl zc st x xl xc y yl yc).mono
    (fun _ ⟨h1, h2, h3, h4, h5⟩ => q_pre h1 h2 h3 h4 h5) (fun _ _ _ hq => ⟨(q_post hq).1, q_exact hq⟩)

/-- **`nat.mul`** (arm64) with the exact-write clause, `MulPre` operands (`MulHypQE`, = `hypQE0.toQE`) -/
theorem hypQE (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypQE impl R names mulWX 88 mulCQ :=
  (hypQE0 impl hap R hmk hgr hmc hmv hwb).toQE

end FvModexp.Arm64.Q.NatMul
