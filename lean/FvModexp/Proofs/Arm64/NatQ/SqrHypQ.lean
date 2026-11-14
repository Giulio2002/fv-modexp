import FvModexp.Proofs.Arm64.NatQ.NatSqr
import FvModexp.Proofs.Arm64.NatQ.SqrMulQ
import FvModexp.Proofs.Arm64.Nat.SqrWX

set_option autoImplicit false

/-!
# `nat.sqr` (arm64) in the Q-form premise: `Q.NatSqr.hypQ : EvenHyp.SqrHypQ … LibSqr.names (sqrW 4096) 64 sqrCQ`
(TIGHT COSTS; the twin of `NatSqr.hypX`, Nat/SqrHypX.lean): from `Q.NatSqr.ens` at the window `sqrW 4096`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.NatSqr (sqrWX wordT_rt)

set_option maxRecDepth 20000 in
theorem q_pre {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc : Nat} {s : State}
    (h : SqrPre R b (sqrCQ xl + stkR H s.mem st) L sqrWX 64 zp zl zc st x xl s) (hc : CapIn R L x xl xc)
    (hx : SqrX R L s sqrWX 64 st zp zc x xl xc) (hH : stLen s.mem st + 4 * (2 * xl) + 64 ≤ H) :
    SPre R b H L sqrWX zp zc st x xl xc s := by
  obtain ⟨hce, hsv, hglb, -, ⟨hz40, hzl, hzw⟩, ⟨-, hxacc, -, -, hxw⟩, hx12, hal, ⟨hsok, hstw, hstg, hsta⟩, hlen, hza,
    hxa, hcost, hinv⟩ := h
  obtain ⟨hxc, hxc40, hxh, hx48⟩ := hc
  obtain ⟨⟨hst0, hswb, hfh, hfw, hfg, hsf, hsgA, hfgA⟩, hzo, hzx, hzop, hxop⟩ := hx
  have hro : RoOut R := hce.2.2.2.2.2.2.2
  refine ⟨hce, by unfold sqrWX sqrW ksqrW; omega, hsv, hglb, wordT_rt hro, hxc, hxc40, hx12, hxacc,
    fun _ => ⟨hxh, hx48⟩, fun _ => hxw, hz40, hzl, hzo, fun h0 => ⟨(hzw h0).2, ?_, (hzop (by omega)).1, (hzop (by omega)).2⟩,
    ?_, ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩, fun h0 => ⟨?_, (hxop (by omega)).1,
    (hxop (by omega)).2⟩, hlen, ⟨hH, hcost⟩, hinv⟩
  · exact (hza (by omega)).1.symm
  · by_cases he : zp = x
    · exact Or.inl ⟨he, hzx he⟩
    · rcases hal with h1 | h1
      · exact absurd h1 he
      · exact Or.inr h1
  · exact (hxa (by omega)).1.symm

set_option maxRecDepth 20000 in
theorem q_post {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zc st x xl xc : Nat} {s s' : State}
    (h : SPost R b H L sqrWX zp zc st x xl xc s s') :
    SqrPostQ R b (sqrCQ xl + stkR H s.mem st) (stkR H s'.mem st) L sqrWX 64 zp zc st x xl s s' ∧
      Reuse (2 * xl) zp zc [(x, xc)] s' := by
  obtain ⟨p', l', c', r0, r1, r2, hv, hn, hlc, -, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hreu, hsb, hF,
    hLF⟩ := h
  refine ⟨⟨p', l', c', r0, r1, r2, L', b', ⟨hv, hn, hlc, hc40, hlive, hkind⟩, ⟨hext, hbud, hinv⟩, hsb, hfa, hF, hLF⟩,
    fun hn2 hne => ?_⟩
  obtain ⟨e1, e2, -⟩ := hreu hn2 (hne _ List.mem_cons_self)
  subst e1 e2
  exact ⟨r0, r2⟩

/-- **`nat.sqr`** (arm64) in the Q-form premise `SqrHypQ`, window `sqrW 4096`, `above = 64`, cost `sqrCQ` -/
theorem hypQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    SqrHypQ impl R names sqrWX 64 sqrCQ := fun H b L z zl zc st x xl xc =>
  (ens impl hap R hmk hgr hmc hmv hwb H b L sqrWX z zl zc st x xl xc).mono
    (fun _ ⟨h1, h2, h3, h4⟩ => q_pre h1 h2 h3 h4) (fun _ _ _ hq => q_post hq)

end FvModexp.Arm64.Q.NatSqr
