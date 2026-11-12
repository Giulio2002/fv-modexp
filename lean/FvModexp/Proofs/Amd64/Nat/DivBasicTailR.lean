import FvModexp.Proofs.Amd64.Nat.DivBasicRel

set_option autoImplicit false

/-!
# `divBasic` (amd64): the run of the loop tail (natdiv.go:719-722) on a small context (agent top s24)

`tailPt = +0x4c9 → head = +0x1a1`: `ujn = u[j+n-1]`; `if j == m && m == len(q) && qhat == 0 { continue }`;
`q[j] = qhat`; the back edge `+0x168` (`j--` and the head registers reloaded from the frame: `RAX = rec`, `RCX = n`,
`RBX = len qhatv`, `RSI = v.ptr`, `RDI = cap qhatv`, `R10 = qhatv.ptr`, `R8 = ujn`, `R11 = vn1`).
(`RSP` = the entry's; `RAX = n`, `RSI = len u`, `R10 = u.ptr`, `R8 = qhat` on entry.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivBasic

/-- the `continue` of natdiv.go:719 -/
@[reducible] def skipQ (j ul vl ql qh : Nat) : Prop := j = ul - vl ∧ ul - vl = ql ∧ qh = 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem tailRun (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State)
    (sp j vl ul up ql qp qh a0 a3 a6 a7 a10 a11 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 tailPt) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (h0 : S.regs 0 = BitVec.ofNat 64 vl) (h6 : S.regs 6 = BitVec.ofNat 64 ul) (h10 : S.regs 10 = BitVec.ofNat 64 up)
    (h8 : S.regs 8 = BitVec.ofNat 64 qh) (hqh : qh < 2 ^ 64) (hj : j + vl ≤ ul) (hv1 : 1 ≤ vl) (hul : ul < 2 ^ 40)
    (hqlb : ql < 2 ^ 40) (hst : ¬ skipQ j ul vl ql qh → j < ql)
    (hu48 : up + 8 * ul ≤ 2 ^ 48) (huacc : S.mem.accessible up (8 * ul) false = true)
    (hq48 : qp + 8 * ql ≤ 2 ^ 48) (hqacc : S.mem.accessible qp (8 * ql) true = true)
    (hqw : qp + 8 * ql ≤ sp - 4424 ∨ sp + 88 ≤ qp)
    (m96 : S.mem.readLE (sp - 96) 8 = j) (m104 : S.mem.readLE (sp - 104) 8 = ul - vl)
    (m40 : S.mem.readLE (sp + 40) 8 = ql) (m32 : S.mem.readLE (sp + 32) 8 = qp)
    (m136 : S.mem.readLE (sp - 136) 8 = a0) (m16 : S.mem.readLE (sp + 16) 8 = vl)
    (m120 : S.mem.readLE (sp - 120) 8 = a3) (m8 : S.mem.readLE (sp + 8) 8 = a6)
    (m64 : S.mem.readLE (sp - 64) 8 = a7) (m56 : S.mem.readLE (sp - 56) 8 = a10)
    (m72 : S.mem.readLE (sp - 72) 8 = a11)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 head → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 0 = BitVec.ofNat 64 a0 → S'.regs 1 = BitVec.ofNat 64 vl →
      S'.regs 2 = BitVec.ofNat 64 (j + 2 ^ 64 - 1) → S'.regs 3 = BitVec.ofNat 64 a3 →
      S'.regs 6 = BitVec.ofNat 64 a6 → S'.regs 7 = BitVec.ofNat 64 a7 →
      S'.regs 8 = BitVec.ofNat 64 (S.mem.readLE (up + 8 * (j + vl - 1)) 8) →
      S'.regs 10 = BitVec.ofNat 64 a10 → S'.regs 11 = BitVec.ofNat 64 a11 →
      S'.mem = (if skipQ j ul vl ql qh then S.mem else S.mem.writeLE (qp + 8 * j) 8 qh) → S'.xmm = S.xmm →
      S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e96 : S.mem.readLE ((S.regs 4).toNat + 128) 8 = j := by rw [show (S.regs 4).toNat + 128 = sp - 96 by omega]; exact m96
  have e104 : S.mem.readLE ((S.regs 4).toNat + 120) 8 = ul - vl := by
    rw [show (S.regs 4).toNat + 120 = sp - 104 by omega]; exact m104
  have e40 : S.mem.readLE ((S.regs 4).toNat + 264) 8 = ql := by rw [show (S.regs 4).toNat + 264 = sp + 40 by omega]; exact m40
  have e32 : S.mem.readLE ((S.regs 4).toNat + 256) 8 = qp := by rw [show (S.regs 4).toNat + 256 = sp + 32 by omega]; exact m32
  have e136 : S.mem.readLE ((S.regs 4).toNat + 88) 8 = a0 := by rw [show (S.regs 4).toNat + 88 = sp - 136 by omega]; exact m136
  have e16 : S.mem.readLE ((S.regs 4).toNat + 240) 8 = vl := by rw [show (S.regs 4).toNat + 240 = sp + 16 by omega]; exact m16
  have e120 : S.mem.readLE ((S.regs 4).toNat + 104) 8 = a3 := by rw [show (S.regs 4).toNat + 104 = sp - 120 by omega]; exact m120
  have e8 : S.mem.readLE ((S.regs 4).toNat + 232) 8 = a6 := by rw [show (S.regs 4).toNat + 232 = sp + 8 by omega]; exact m8
  have e64 : S.mem.readLE ((S.regs 4).toNat + 160) 8 = a7 := by rw [show (S.regs 4).toNat + 160 = sp - 64 by omega]; exact m64
  have e56 : S.mem.readLE ((S.regs 4).toNat + 168) 8 = a10 := by rw [show (S.regs 4).toNat + 168 = sp - 56 by omega]; exact m56
  have e72 : S.mem.readLE ((S.regs 4).toNat + 152) 8 = a11 := by rw [show (S.regs 4).toNat + 152 = sp - 72 by omega]; exact m72
  have hu1 : S.mem.readLE (up + (vl + j - 1) * 8) 8 = S.mem.readLE (up + 8 * (j + vl - 1)) 8 := by congr 1; omega
  janus64_run [h0, h6, h10, h8, e96, e104, e40, e32, e136, e16, e120, e8, e64, e56, e72, hu1] until [head]
  all_goals
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
    · janus64_simp
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply congrArg (BitVec.ofNat 64); apply congrArg (fun a => Janus.Arm64.Memory.readLE S.mem a 8); omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · show _ = _
      by_cases hs : skipQ j ul vl ql qh
      · simp only [eq_true hs, ite_true]
        all_goals (exfalso; simp only [skipQ] at hs; omega)
      · simp only [eq_false hs, ite_false]
        all_goals first | (exfalso; apply hs; simp only [skipQ]; omega) | rw [show qp + j * 8 = qp + 8 * j by omega]

end FvModexp.Amd64.DivBasic
