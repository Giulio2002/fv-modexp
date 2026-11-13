import FvModexp.Proofs.Amd64.NatQ.DivBasicHdM

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivBasicPro3.lean, TIGHT COSTS, top s38)
# `divBasic` (amd64): `pro3` — from `stk.nat`'s return to the loop head (`Hd`)

Composes `recRun` (the run of the inlined `reciprocalWord`, DivBasicRec) with the pure memory facts `head_mem` /
`head_qu` (DivBasicHdM).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.DivBasic
open FvModexp.Amd64.DivBasic
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- after `stk.nat` returned (`S2`): `vn1 := v[n-1]`, the inlined `reciprocalWord`, `j := m`, `ujn := 0` → the head -/
theorem pro3 (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc : BitVec 64) (vp vl : Nat) (s : State)
    (hpre : Pre R b H L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s)
    (hx15s : s.xmm 15 = 0#128) (hdfs : s.df = false) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (P : State) (hP : AtNat R b L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl s P)
    (S2 : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (hA : AfterNat R b H L st.toNat vl s P S2 L1 b1) (Q : State → Prop)
    (k : ∀ S t w1 c1, Hd R b H L qp.toNat ql.toNat st.toNat up.toNat ul.toNat uc.toNat vp vl
      (s.mem.readLE ((s.regs 4).toNat + 24) 8) s t L1 b1 w1 c1 S (ul.toNat + 2 ^ 64 - vl) 0 →
      (∀ a n, (qp.toNat ≤ a ∧ a + n ≤ qp.toNat + 8 * ql.toNat) ∨ (up.toNat ≤ a ∧ a + n ≤ up.toNat + 8 * ul.toNat) →
        S.mem.readLE a n = s.mem.readLE a n) →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S2 Q := by
  have hacc : ∀ a n v, S2.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hA.F2.accessible, Janus.Arm64.Memory.accessible_writeLE, hP.fr.accessible]
  have hE := env_of (S2 := S2.mem) hpre hA.ext hA.bud hA.ok hA.len hA.same hA.grow hacc hA.mem hx15s hdfs hra
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have ht48 := hl.t48
  have hwacc : S2.mem.accessible ((s.regs 4).toNat - 4424) (4424 + 88) true = true := by
    rw [hacc]; exact hpre.ce.2.1.2.2
  have hvacc : S2.mem.accessible vp (8 * vl) false = true := by rw [hacc]; exact hpre.vacc
  have q16 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = vl := by
    rw [rdS2 hpre hA _ _ (by omega) (by omega), rdP hP.fr _ _ (by omega)]; exact hpre.vlS
  have q8 : S2.mem.readLE ((s.regs 4).toNat + 8) 8 = vp := by
    rw [rdS2 hpre hA _ _ (by omega) (by omega), rdP hP.fr _ _ (by omega)]; exact hpre.vpS
  have qn1 := (rdS2 hpre hA ((s.regs 4).toNat - 64) 8 (by omega) (by omega)).trans hP.n1
  have hvn1 : S2.mem.readLE (vp + vl * 8 - 8) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8 := by
    rw [show vp + vl * 8 - 8 = vp + 8 * (vl - 1) by omega]
    exact rdS2v hpre hP hA hE _ _ (Or.inl ⟨by omega, by omega⟩)
  have hV64 : s.mem.readLE (vp + 8 * (vl - 1)) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hM := head_mem hpre hP hA hE rfl rfl
  have hQU := head_qu hpre hP hA hE (s.mem.readLE (vp + 8 * (vl - 1)) 8)
    (AsmDiv.recipWord (s.mem.readLE (vp + 8 * (vl - 1)) 8))
  refine recRun impl _ Q s S2 vp vl _ (s.mem.readLE (vp + 8 * (vl - 1)) 8) _ hsp0 hsp1 hA.pc hA.sp hA.r0 hA.r1 hA.r3
    hv2 hl.vb (by omega) hl.v48 hwacc hvacc q16 q8 qn1
    ((rdS2 hpre hA ((s.regs 4).toNat - 104) 8 (by omega) (by omega)).trans hP.mm) (Nat.mod_lt _ (by omega)) hvn1
    hpre.vtop hV64 ?_
  intro S e0 e4 e5 e14 efs ex edf er0 er1 er2 er3 er6 er7 er8 er10 er11 em
  refine k S _ _ _ ⟨e0, by rw [e4, hA.sp], by rw [e5, hA.r5], by rw [e14, hA.r14], by rw [efs, hA.fs],
    by rw [ex, hA.x15], by rw [edf, hA.df], er0, er1, ?r2, er3, er6, er7, by rw [er8], er10, er11, hE,
    by rw [em]; exact hM⟩ (by rw [em]; exact hQU)
  case r2 =>
    rw [er2]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

end FvModexp.Amd64.Q.DivBasic
