import FvModexp.Proofs.Amd64.NatQ.DivBasicRel
import FvModexp.Proofs.Amd64.NatQ.DivBasicCallees
import FvModexp.Proofs.Amd64.NatQ.DivBasicMemF

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivBasicAddR.lean, TIGHT COSTS, top s38)
# `divBasic` (amd64): the runs of the add-back (natdiv.go:710-716) on small contexts (agent top s24)

`add0Run`: `afterSub = +0x3bc → tailPt = +0x4c9` when the borrow `c = 0` (`RAX = n`, `RSI = len u`, `R10 = u.ptr`,
`R8 = qhat`). `addRun`: `c ≠ 0`: `j + n → RSP-88`, the ABI0 frame `[RSP-224, RSP-152)` = `(&u[j], n, cap u - j, &u[j],
n, cap u - j, v.ptr, n, cap v)`, `CALL addVV.abi0` (carry at `RSP-152`), `XORPS X15; MOVQ FS:-8, R14` → `afterAdd =
+0x472`. `addFin`: `afterAdd → tailPt`: `u[j+n] += c` when `n < qhl`, `R8 = qhat - 1`. (`RSP` = the entry's.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.DivBasic
open FvModexp.Amd64.DivBasic
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem add0Run (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State) (sp vl ul up qhat : Nat)
    (hpc : S.rip = BitVec.ofNat 64 afterSub) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (m152 : S.mem.readLE (sp - 152) 8 = 0) (m16 : S.mem.readLE (sp + 16) 8 = vl)
    (m72 : S.mem.readLE (sp + 72) 8 = ul) (m64 : S.mem.readLE (sp + 64) 8 = up)
    (m112 : S.mem.readLE (sp - 112) 8 = qhat)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 tailPt → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 0 = BitVec.ofNat 64 vl → S'.regs 6 = BitVec.ofNat 64 ul →
      S'.regs 10 = BitVec.ofNat 64 up → S'.regs 8 = BitVec.ofNat 64 qhat → S'.mem = S.mem → S'.xmm = S.xmm →
      S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e152 : S.mem.readLE ((S.regs 4).toNat + 72) 8 = 0 := by rw [show (S.regs 4).toNat + 72 = sp - 152 by omega]; exact m152
  have e16 : S.mem.readLE ((S.regs 4).toNat + 240) 8 = vl := by rw [show (S.regs 4).toNat + 240 = sp + 16 by omega]; exact m16
  have e72 : S.mem.readLE ((S.regs 4).toNat + 296) 8 = ul := by rw [show (S.regs 4).toNat + 296 = sp + 72 by omega]; exact m72
  have e64 : S.mem.readLE ((S.regs 4).toNat + 288) 8 = up := by rw [show (S.regs 4).toNat + 288 = sp + 64 by omega]; exact m64
  have e112 : S.mem.readLE ((S.regs 4).toNat + 112) 8 = qhat := by
    rw [show (S.regs 4).toNat + 112 = sp - 112 by omega]; exact m112
  janus64_run [e152, e16, e72, e64, e112] until [tailPt]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
  · janus64_simp
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
theorem addRun (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b1 : Nat) (L1 : List (Nat × Nat)) (r : Nat) (Q : State → Prop) (S : State) (sp vl j z uc vp vc bw : Nat)
    (hpc : S.rip = BitVec.ofNat 64 afterSub) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (hvb : vl + 4 ≤ 2 ^ 16) (hjq : j + vl ≤ uc) (huc : uc < 2 ^ 40) (hbw : bw ≠ 0) (hbw64 : bw < 2 ^ 64) (hz64 : z < 2 ^ 64)
    (hvp64 : vp < 2 ^ 64)
    (m152 : S.mem.readLE (sp - 152) 8 = bw) (m96 : S.mem.readLE (sp - 96) 8 = j)
    (m16 : S.mem.readLE (sp + 16) 8 = vl) (m80 : S.mem.readLE (sp + 80) 8 = uc)
    (m48 : S.mem.readLE (sp - 48) 8 = z) (m80' : S.mem.readLE (sp - 80) 8 = uc - j)
    (m8 : S.mem.readLE (sp + 8) 8 = vp) (m24 : S.mem.readLE (sp + 24) 8 = vc)
    (hzacc : S.mem.accessible z (8 * vl) true = true) (hvacc : S.mem.accessible vp (8 * vl) false = true)
    (hzv : Apart z (8 * vl) vp (8 * vl))
    (hzw : z + 8 * vl ≤ sp - 4424 ∨ sp + 88 ≤ z) (hvw : vp + 8 * vl ≤ sp - 4424 ∨ sp + 88 ≤ vp)
    (hzH : Held R L1 z (8 * vl)) (hinv : R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 S.mem))
    (hout : Outside (sp - 4424) (4424 + 88) R.rt)
    (hgw : Apart ((S.regs 14).toNat + 16) 8 (sp - 4424) (4424 + 88))
    (hzg : Apart z (8 * vl) ((S.regs 14).toNat + 16) 8)
    (htl : TlsG S) (hlw : Apart (S.fsBase.toNat - 8) 8 (sp - 4424) (4424 + 88))
    (hzl : Apart z (8 * vl) (S.fsBase.toNat - 8) 8)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 afterAdd → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.xmm 15 = 0#128 → S'.fsBase = S.fsBase → S'.df = S.df →
      natVal S'.mem z vl = (natVal S.mem z vl + natVal S.mem vp vl) % 2 ^ (64 * vl) →
      S'.mem.readLE (sp - 152) 8 = (natVal S.mem z vl + natVal S.mem vp vl) / 2 ^ (64 * vl) →
      S'.mem.readLE (sp - 88) 8 = j + vl →
      MemFrame S.mem S'.mem [(sp - 232, sp - 144), (sp - 88, sp - 80), (z, z + 8 * vl)] →
      ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e152 : S.mem.readLE ((S.regs 4).toNat + 72) 8 = bw := by rw [show (S.regs 4).toNat + 72 = sp - 152 by omega]; exact m152
  have e96 : S.mem.readLE ((S.regs 4).toNat + 128) 8 = j := by rw [show (S.regs 4).toNat + 128 = sp - 96 by omega]; exact m96
  have e16 : S.mem.readLE ((S.regs 4).toNat + 240) 8 = vl := by rw [show (S.regs 4).toNat + 240 = sp + 16 by omega]; exact m16
  have e80 : S.mem.readLE ((S.regs 4).toNat + 304) 8 = uc := by rw [show (S.regs 4).toNat + 304 = sp + 80 by omega]; exact m80
  have e48 : S.mem.readLE ((S.regs 4).toNat + 176) 8 = z := by rw [show (S.regs 4).toNat + 176 = sp - 48 by omega]; exact m48
  have e80' : S.mem.readLE ((S.regs 4).toNat + 144) 8 = uc - j := by
    rw [show (S.regs 4).toNat + 144 = sp - 80 by omega]; exact m80'
  have e8 : S.mem.readLE ((S.regs 4).toNat + 232) 8 = vp := by rw [show (S.regs 4).toNat + 232 = sp + 8 by omega]; exact m8
  have e24 : S.mem.readLE ((S.regs 4).toNat + 248) 8 = vc := by rw [show (S.regs 4).toNat + 248 = sp + 24 by omega]; exact m24
  have hzx : z = z ∨ Apart z (8 * vl) z (8 * vl) := Or.inl rfl
  have hzv' : z = vp ∨ Apart z (8 * vl) vp (8 * vl) := Or.inr hzv
  have hzacc' : S.mem.accessible z (8 * vl) false = true := Janus.Arm64.Memory.accessible_read_of_write _ hzacc
  have hvw' := view_win hout L1
  have hfa := htl.addr
  obtain ⟨⟨hfb1, hfb2⟩, hfacc, hfg⟩ := htl
  unfold Apart at hzv hgw hzg hlw hzl
  janus64_run [e152, e96, e16, e80, e48, e80', e8, e24, hvw', hfa] until [afterAdd] calls [addvv impl hap R b1 L1]
  rename_i _ _ _ _ _ m _ _ hv hc hfr _ _ _
  have hfr' : MemFrame S.mem m [(sp - 232, sp - 144), (sp - 88, sp - 80), (z, z + 8 * vl)] := by
    refine ⟨fun a n ho => ?_, fun a n v => ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at ho
      obtain ⟨o1, o2, o3⟩ := ho
      rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
  have e152' : sp - 152 = (S.regs 4).toNat - 8 + 80 := by omega
  refine k _ ?_ ?_ ?_ ?_ ?_ rfl rfl hv (by rw [e152']; exact hc) ?_ hfr'
  · janus64_simp
  · simp only [setRegF_apply, regs0, regSP, Nat.reduceEqDiff, ↓reduceIte]; exact BitVec.sub_add_cancel _ _
  · simp only [setRegF_apply, regs0, regSP, regFP, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, regG, ↓reduceIte]
  · simp only [setXmmF, ↓reduceIte]
  · rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      show sp - 88 = (S.regs 4).toNat + 136 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem addFin (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State) (sp vl ul up j q ca qhat : Nat)
    (hpc : S.rip = BitVec.ofNat 64 afterAdd) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (hvb : vl + 4 ≤ 2 ^ 16) (hq : q = vl ∨ q = vl + 1) (hjq : j + q ≤ ul) (hul : ul < 2 ^ 40)
    (hu48 : up + 8 * ul ≤ 2 ^ 48) (huacc : S.mem.accessible up (8 * ul) true = true)
    (huw : up + 8 * ul ≤ sp - 4424 ∨ sp + 88 ≤ up)
    (m16 : S.mem.readLE (sp + 16) 8 = vl) (m128 : S.mem.readLE (sp - 128) 8 = q)
    (m72 : S.mem.readLE (sp + 72) 8 = ul) (m88 : S.mem.readLE (sp - 88) 8 = j + vl)
    (m152 : S.mem.readLE (sp - 152) 8 = ca) (m64 : S.mem.readLE (sp + 64) 8 = up)
    (m112 : S.mem.readLE (sp - 112) 8 = qhat)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 tailPt → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 0 = BitVec.ofNat 64 vl → S'.regs 6 = BitVec.ofNat 64 ul →
      S'.regs 10 = BitVec.ofNat 64 up → S'.regs 8 = BitVec.ofNat 64 qhat - 1#64 →
      S'.mem = (if vl < q then S.mem.writeLE (up + 8 * (j + vl)) 8 (S.mem.readLE (up + 8 * (j + vl)) 8 + ca)
        else S.mem) → S'.xmm = S.xmm →
      S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e16 : S.mem.readLE ((S.regs 4).toNat + 240) 8 = vl := by rw [show (S.regs 4).toNat + 240 = sp + 16 by omega]; exact m16
  have e128 : S.mem.readLE ((S.regs 4).toNat + 96) 8 = q := by rw [show (S.regs 4).toNat + 96 = sp - 128 by omega]; exact m128
  have e72 : S.mem.readLE ((S.regs 4).toNat + 296) 8 = ul := by rw [show (S.regs 4).toNat + 296 = sp + 72 by omega]; exact m72
  have e88 : S.mem.readLE ((S.regs 4).toNat + 136) 8 = j + vl := by
    rw [show (S.regs 4).toNat + 136 = sp - 88 by omega]; exact m88
  have e152 : S.mem.readLE ((S.regs 4).toNat + 72) 8 = ca := by rw [show (S.regs 4).toNat + 72 = sp - 152 by omega]; exact m152
  have e64 : S.mem.readLE ((S.regs 4).toNat + 288) 8 = up := by rw [show (S.regs 4).toNat + 288 = sp + 64 by omega]; exact m64
  have e112 : S.mem.readLE ((S.regs 4).toNat + 112) 8 = qhat := by
    rw [show (S.regs 4).toNat + 112 = sp - 112 by omega]; exact m112
  have hqv : q < 2 ^ 63 := by omega
  have hvq : vl < 2 ^ 63 := by omega
  have hcam : ca % 18446744073709551616 = ca := Nat.mod_eq_of_lt (m152 ▸ Janus.Arm64.Memory.readLE_lt _ _ 8)
  rcases hq with rfl | rfl
  · janus64_run [e16, e128, e72, e88, e152, e64, e112] until [tailPt]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
    · janus64_simp
    any_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    simp only [show (q < q) = False from eq_false (Nat.lt_irrefl q), ite_false]
  · janus64_run [e16, e128, e72, e88, e152, e64, e112, hcam] until [tailPt]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
    · janus64_simp
    any_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    show Arm64.Memory.writeLE _ _ _ _ = _
    simp only [show (vl < vl + 1) = True from eq_true (by omega), ite_true]
    rw [show up + 8 * (j + vl) = up + (j + vl) * 8 by omega]

/-- what the continuation of the add-back gets (`S` at `afterSub`, `S'` at `tailPt`; the twin of the arm64 `AddK`) -/
@[reducible] def AddK (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S S' : State) (j qhat q bw : Nat) : Prop :=
  Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' tailPt j ∧ S'.regs 0 = BitVec.ofNat 64 vl ∧
    S'.regs 6 = BitVec.ofNat 64 ul ∧ S'.regs 10 = BitVec.ofNat 64 up ∧
    S'.regs 8 = BitVec.ofNat 64 (if bw = 0 then qhat else (qhat + 2 ^ 64 - 1) % 2 ^ 64) ∧
    MemFrame S.mem S'.mem (scr s ++ [(up + 8 * j, up + 8 * j + 8 * q)]) ∧
    (bw = 0 → ∀ a n, S'.mem.readLE a n = S.mem.readLE a n) ∧
    (bw ≠ 0 → ∃ ca, natVal S'.mem (up + 8 * j) vl + 2 ^ (64 * vl) * ca = natVal S.mem (up + 8 * j) vl + natVal s.mem vp vl ∧
      (vl < q → S'.mem.readLE (up + 8 * j + 8 * vl) 8 = (S.mem.readLE (up + 8 * j + 8 * vl) 8 + ca) % 2 ^ 64))

end FvModexp.Amd64.Q.DivBasic
