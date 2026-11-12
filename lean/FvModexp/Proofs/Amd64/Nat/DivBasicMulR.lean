import FvModexp.Proofs.Amd64.Nat.DivBasicRel
import FvModexp.Proofs.Amd64.Nat.DivBasicCallees

set_option autoImplicit false

/-!
# `divBasic` (amd64): the run `mulPt → afterVww` on a small context (agent top s23)

`CMPQ DI, CX` (`n ≤ cap qhatv`), `qhat` spilled at `RSP-112`, the ABI0 frame `[RSP-224, RSP-160)` =
`(t, n, n+1, vp, n, vc, qhat, 0)`, `CALL mulAddVWW.abi0` (return slot `RSP-232`, carry at `RSP-160`), then
`XORPS X15, X15; MOVQ FS:-8, R14`. (`RSP` = the entry's.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
theorem mulRun (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b1 : Nat) (L1 : List (Nat × Nat)) (r : Nat) (Q : State → Prop) (S : State) (sp t vl vp vc qhat : Nat)
    (hpc : S.rip = BitVec.ofNat 64 mulPt) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (h8 : S.regs 8 = BitVec.ofNat 64 qhat) (h10 : S.regs 10 = BitVec.ofNat 64 t) (h1 : S.regs 1 = BitVec.ofNat 64 vl)
    (h7 : S.regs 7 = BitVec.ofNat 64 (vl + 1)) (h6 : S.regs 6 = BitVec.ofNat 64 vp) (hvb : vl + 4 ≤ 2 ^ 16)
    (hq : qhat < 2 ^ 64) (ht64 : t < 2 ^ 64) (hvp64 : vp < 2 ^ 64)
    (m24 : S.mem.readLE (sp + 24) 8 = vc)
    (htacc : S.mem.accessible t (8 * vl) true = true) (hvacc : S.mem.accessible vp (8 * vl) false = true)
    (hty : Apart t (8 * vl) vp (8 * vl)) (htw : t + 8 * vl ≤ sp - 4424 ∨ sp + 88 ≤ t)
    (hvw : vp + 8 * vl ≤ sp - 4424 ∨ sp + 88 ≤ vp)
    (htH : Held R L1 t (8 * vl)) (hinv : R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 S.mem))
    (hout : Outside (sp - 4424) (4424 + 88) R.rt)
    (hgw : Apart ((S.regs 14).toNat + 16) 8 (sp - 4424) (4424 + 88)) (htg : Apart t (8 * vl) ((S.regs 14).toNat + 16) 8)
    (htl : TlsG S) (hlw : Apart (S.fsBase.toNat - 8) 8 (sp - 4424) (4424 + 88))
    (htt : Apart t (8 * vl) (S.fsBase.toNat - 8) 8)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 afterVww → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.xmm 15 = 0#128 → S'.fsBase = S.fsBase → S'.df = S.df →
      natVal S'.mem t vl = natVal S.mem vp vl * qhat % 2 ^ (64 * vl) →
      S'.mem.readLE (sp - 160) 8 = natVal S.mem vp vl * qhat / 2 ^ (64 * vl) →
      S'.mem.readLE (sp - 112) 8 = qhat →
      MemFrame S.mem S'.mem [(sp - 232, sp - 152), (sp - 112, sp - 104), (t, t + 8 * vl)] →
      ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e24 : S.mem.readLE ((S.regs 4).toNat + 248) 8 = vc := by rw [show (S.regs 4).toNat + 248 = sp + 24 by omega]; exact m24
  have hvw' := view_win hout L1
  have hty' : t = vp ∨ Apart t (8 * vl) vp (8 * vl) := Or.inr hty
  have hfa := htl.addr
  obtain ⟨⟨hfb1, hfb2⟩, hfacc, hfg⟩ := htl
  unfold Apart at hty hgw htg hlw htt
  janus64_run [h8, h10, h1, h7, h6, e24, hvw', hfa] until [afterVww] calls [vww impl hap R b1 L1]
  rename_i _ _ _ _ _ m _ _ hv hc hfr _ _ _
  have hfr' : MemFrame S.mem m [(sp - 232, sp - 152), (sp - 112, sp - 104), (t, t + 8 * vl)] := by
    refine ⟨fun a n ho => ?_, fun a n v => ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at ho
      obtain ⟨o1, o2, o3⟩ := ho
      rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
  refine k _ ?gpc ?g4 ?g5 ?g14 ?gx rfl rfl hv ?gc ?gq hfr'
  case gpc => janus64_simp
  case g4 => simp only [setRegF_apply, regs0, regSP, Nat.reduceEqDiff, ↓reduceIte]; exact BitVec.sub_add_cancel _ _
  case g5 => simp only [setRegF_apply, regs0, regSP, regFP, Nat.reduceEqDiff, ↓reduceIte]
  case g14 => simp only [setRegF_apply, regG, ↓reduceIte]
  case gx => simp only [setXmmF, ↓reduceIte]
  case gc => rw [show sp - 160 = (S.regs 4).toNat - 8 + 72 by omega]; exact hc
  case gq =>
    rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      show sp - 112 = (S.regs 4).toNat + 112 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hq

end FvModexp.Amd64.DivBasic
