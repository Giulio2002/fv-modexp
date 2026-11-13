import FvModexp.Proofs.Amd64.NatQ.KMulEndP
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# [amd64 port (divmc s51) of the Q-form Arm64/NatQ/KMulEnd.lean — TIGHT COSTS] `karatsuba` (amd64): the end (natmul.go:217, :250), `KM7 → RET`

`kEnd`: from `KM7` (`0x5f2245`) the `addTo(z[n2:], z1.abs)` arguments (no bounds check on amd64), the call
(`kn_addcall`), the defer-bit store, the deferred closure `karatsuba.deferwrap1` (`kndsum`, `kn_restcall`),
`ADDQ`/`POPQ BP`/`RET` → `Kept` + `KPost` (`knEndFin`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

def fnKD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba.deferwrap1"

set_option maxRecDepth 20000 in
/-- the deferred `stk.restore` closure of `karatsuba` as a callee of `LibMul` (as `NatSqr.kdsum`) -/
theorem kndsum (impl : List Amd64.Segment) :
    Summary (LibMul.program.link impl) (segAddr LibMul.program fnKD) Restore.Pre Restore.Post := by
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

theorem kndsum_entry : segAddr LibMul.program fnKD = kDfn := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem kEnd (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (hra0 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (S : State)
    (hB : KM7 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk l) :
    KNGoal impl R H b L W st zp xp n yp s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hkn : n ≤ 2 * kh n ∧ 2 * kh n ≤ n + 1 := by simp only [kh]; omega
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hl := hB.hl
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨-, e1, e2, e3⟩ := hB.z1h
  rw [show (s.regs 4).toNat - 264 + 8 = (s.regs 4).toNat - 256 by omega] at e1
  rw [show (s.regs 4).toNat - 264 + 16 = (s.regs 4).toNat - 248 by omega] at e2
  rw [show (s.regs 4).toNat - 264 + 24 = (s.regs 4).toNat - 240 by omega] at e3
  have f3 := hkm.s3; have f1 := hkm.q104; have f4 := hkm.q88; have f5 := hkm.q112
  have hwA : S.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := by
    rw [hkm.fr.accessible]; exact hkm.F.env.2.1.2.2
  have hsub : ∀ a c : Nat, c ≤ a → a < 2 ^ 64 → BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
    intro a c h1 h2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hD := kndsum impl
  rw [kndsum_entry] at hD
  unfold KNGoal
  janus64_run [hsp', f1, f3, f4, f5, e1, e2, e3] until [kAddToA]
  refine kn_addcall impl hap R hmv hB hx150 hdf0 _ rfl ?sp ?g ?h5 ?fs ?df ?x15 ?m ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?cont
  case cont =>
    intro s2 hA2 hreg2 Lk' bk' hkmA hz
    obtain ⟨k0, k4, k14, k5, kfs, kdf, kx15⟩ := hA2
    have hp1 := hkmA.dpt
    have hp2 : s2.mem.readLE ((s.regs 4).toNat - 232) 8 = 0x5f2340 := hkmA.dfn
    have hwB : s2.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := by
      rw [hkmA.fr.accessible]; exact hkmA.F.env.2.1.2.2
    have hsp2 : (s2.regs 4).toNat = (s.regs 4).toNat - 448 := by
      rw [k4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    clear hwA f1 f3 f4 f5 e1 e2 e3
    janus64_run [hp1, hp2, hsp2] until [0x5f2340]
    refine kn_restcall impl hD hkmA hz _ rfl ?sp2 ?h2 ?hF2 ?hra2 ?cont2
    case cont2 =>
      intro s3 q0 q4 q5 q14 q15 qfs qdf hfp hlr hacc3 hpost
      have hwC : s3.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := by rw [hacc3]; exact hwB
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

end FvModexp.Amd64.Q.NatMul
