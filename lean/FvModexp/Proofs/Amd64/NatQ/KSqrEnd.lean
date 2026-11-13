import FvModexp.Proofs.Amd64.NatQ.KSqrEndP
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.DivmcBits

/-!
# [amd64 port (divmc s39) of the Q-form Arm64/NatQ/KSqrEnd.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the end (natmul.go:304, :332), `KB7 → RET`

`kEnd`: from `KB7` (`0x5f271d`) through the `z[n2:]` bounds check (panic refuted), `addTo(z[n2:], z1.abs)`
(`ks_addcall`), the defer-bit store, the deferred closure `karatsubaSqr.deferwrap1` (`kdsum`, `ks_restcall`),
`ADDQ`/`POPQ BP`/`RET` → `Kept` + `KPost` (`kEndFin`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

def fnKD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr.deferwrap1"

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore` closure of `karatsubaSqr` as a callee of `LibSqr` (as `BasicSqr.dsum`) -/
theorem kdsum (impl : List Amd64.Segment) :
    Summary (LibSqr.program.link impl) (segAddr LibSqr.program fnKD) Restore.Pre Restore.Post := by
  intro s hpc ⟨⟨hb, ha, hw⟩, hal, hra, hf1, hf2, hs1, hs2, hn, hsa, hfa⟩
  simp only [regSP] at hb ha hw
  have hsa' := hsa
  have hfa' := hfa
  unfold Apart at hsa' hfa'
  simp only [fnKD, reduceSegAddr] at hpc
  janus64_run
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, by janus_frame⟩
  · simp [setRegF]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  simp only [Nat.reducePow]
  have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 16) 8
  omega

theorem kdsum_entry : segAddr LibSqr.program fnKD = kDfn := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kEnd (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (hra0 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (S : State)
    (hB : KB7 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk l) :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  have hl := hB.hl
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨-, e1, e2, e3⟩ := hB.z1h
  rw [show (s.regs 4).toNat - 200 + 8 = (s.regs 4).toNat - 192 by omega] at e1
  rw [show (s.regs 4).toNat - 200 + 16 = (s.regs 4).toNat - 184 by omega] at e2
  rw [show (s.regs 4).toNat - 200 + 24 = (s.regs 4).toNat - 176 by omega] at e3
  have f3 := hkm.s3; have f1 := hkm.n1s; have f4 := hkm.s4; have f2 := hkm.n2s; have f5 := hkm.s2
  have hwA : S.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := by
    rw [hkm.fr.accessible]; exact hkm.pre.1.2.1.2.2
  have hmask : ((0#64 - (BitVec.ofNat 64 zc - BitVec.ofNat 64 (kn2 n))).sshiftRight 63 &&& BitVec.ofNat 64 (8 * kn2 n)) =
      BitVec.ofNat 64 (8 * kn2 n) := by
    have hd : (BitVec.ofNat 64 zc - BitVec.ofNat 64 (kn2 n)).toNat = zc - kn2 n := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    exact neg_sshr63_and _ _ (by rw [hd]; omega) (by rw [hd]; omega)
  have hsub : ∀ a c : Nat, c ≤ a → a < 2 ^ 64 → BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
    intro a c h1 h2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hD := kdsum impl
  rw [kdsum_entry] at hD
  unfold KGoal
  janus64_run [hsp', hmask, f1, f2, f3, f4, f5, e1, e2, e3] until [addToA]
  refine ks_addcall impl hap R hmv hB hx150 hdf0 _ rfl ?sp ?g ?h5 ?fs ?df ?x15 ?m ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?cont
  case cont =>
    intro s2 hA2 hreg2 Lk' bk' hkmA hz
    obtain ⟨k0, k4, k14, k5, kfs, kdf, kx15⟩ := hA2
    have hp1 := hkmA.dpt
    have hp2 : s2.mem.readLE ((s.regs 4).toNat - 168) 8 = 0x5f2840 := hkmA.dfn
    have hwB : s2.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := by
      rw [hkmA.fr.accessible]; exact hkmA.pre.1.2.1.2.2
    have hsp2 : (s2.regs 4).toNat = (s.regs 4).toNat - 312 := by
      rw [k4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    clear hwA f1 f2 f3 f4 f5 e1 e2 e3
    janus64_run [hp1, hp2, hsp2] until [0x5f2840]
    refine ks_restcall impl hD hkmA hz _ rfl ?sp2 ?h2 ?hF2 ?hra2 ?cont2
    case cont2 =>
      intro s3 q0 q4 q5 q14 q15 qfs qdf hfp hlr hacc3 hpost
      have hwC : s3.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := by rw [hacc3]; exact hwB
      clear hp1 hp2 hwB
      janus64_run [hfp, hlr, hra0]
      refine ⟨⟨by simp [setRegF], by simp [setRegF], ?_, ?_⟩, hpost _ rfl ?_ ?_⟩
      · simp only [setRegF, q14]; simp [setRegF]; exact k14
      · show s3.xmm 15 = s.xmm 15
        rw [q15]; exact kx15
      · show s3.fsBase = s.fsBase
        rw [qfs]; exact kfs
      · rw [hdf0]
    case hF2 => janus_frame
    all_goals (try janus64_simp)
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | (rw [← BitVec.ofNat_add]) |
    exact hsub _ _ (by omega) (by omega) | omega

end FvModexp.Amd64.Q.NatSqr
