import FvModexp.Proofs.Amd64.Exp.P2DPost
import FvModexp.Proofs.Amd64.Exp.P2DRun

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `return z[:0]` (agent asm s67; amd64 twin of infra's arm64 `P2DZero`)

`epi_of`: the epilogue facts on the post-prologue memory `W0` (frame base `sp = RSP - 0x70`). `postE`: a state after
the epilogue (`Epi`) with the result `(zp, l, zc)` and a memory changed only in the own frame (and `z`'s array) gives
`PostD` (through `post_own`). `zeroP` (`zeroE`, `AX = z.ptr`) / `zero2P` (`zero2`, `R13 = z.ptr`): `z[:0]` on the
memory `W0`, value `0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

theorem w0_ra {M : Memory} {sp bp zp xp : Nat} : (W0 M sp bp zp xp).readLE (sp + 0x70) 8 = M.readLE (sp + 0x70) 8 := by
  simp (disch := omega) only [W0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

/-- the epilogue facts on `W0` -/
theorem epi_of (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    (s.regs 4).toNat - 0x70 + 0x78 ≤ 2 ^ 48 ∧
      (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp).accessible ((s.regs 4).toNat - 0x70 + 0x68) 16
        false = true ∧
      (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp).readLE ((s.regs 4).toNat - 0x70 + 0x68) 8 =
        (s.regs 5).toNat ∧
      (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp).readLE ((s.regs 4).toNat - 0x70 + 0x70) 8 =
        (retAddrOf s).toNat ∧ (retAddrOf s).toNat < 2 ^ 47 := by
  obtain ⟨⟨⟨-, ⟨hbel, h48, hacc⟩, -⟩, -⟩, -⟩ := hP
  simp only [regSP] at hbel h48 hacc
  have hrt : (retAddrOf s).toNat = s.mem.readLE (s.regs 4).toNat 8 := by
    simp only [retAddrOf, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, ?_, w0_bp (BitVec.isLt _), ?_, by omega⟩
  · simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
  · rw [w0_ra, hrt, show (s.regs 4).toNat - 0x70 + 0x70 = (s.regs 4).toNat by omega]

/-- the own-frame writes of the prologue -/
theorem w0_own (hk : 8 ≤ stk) (hA : 72 ≤ A) (hsp : 0x70 ≤ (s.regs 4).toNat) :
    MemFrame s.mem (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) (ownW s stk A) :=
  (w0_frame s.mem _ _ _ _).mono fun a k ho => by
    simp only [ownW, outside_cons, outside_nil, and_true] at ho ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the post after the epilogue of an own-frame path** -/
theorem postE (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    {S s' : State} (hE : Epi S s' ((s.regs 4).toNat - 0x70) (s.regs 5).toNat)
    (e14 : S.regs 14 = s.regs 14) (efs : S.fsBase = s.fsBase) (ex : S.xmm 15 = s.xmm 15) (edf : S.df = s.df)
    {M' : Memory} {zs : List (Nat × Nat)} (hF : MemFrame s.mem M' (ownW s stk A ++ zs))
    (hzs : ∀ r ∈ zs, r = (zp, zp + 8 * zc) ∧ 0 < zc)
    {v l : Nat} (hl : l ≤ zc) (hv : natVal M' zp l = v) (hn : NatNorm M' zp l) (hm : s'.mem = M')
    (e0 : s'.regs 0 = BitVec.ofNat 64 zp) (e3 : s'.regs 3 = BitVec.ofNat 64 l) (e1 : s'.regs 1 = BitVec.ofNat 64 zc) :
    PostD R b L stk A cst zp zc st v s s' := by
  obtain ⟨h4, h5, h14, hfs, hx, hdf⟩ := hE
  have hC := hP.1
  obtain ⟨⟨⟨-, ⟨hbel, h48, -⟩, -⟩, -⟩, -⟩ := hP
  try simp only [regSP] at hbel h48
  have h5' : BitVec.ofNat 64 (s.regs 5).toNat = s.regs 5 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (BitVec.isLt _))
  refine ⟨⟨?_, h5.trans h5', h14.trans e14, hx.trans ex⟩,
    post_own hC (by omega) hF hzs hl hv hn hm (hfs.trans efs) (hdf.trans edf) e0 e3 e1⟩
  rw [h4]; bv_omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`return z[:0]`** from `zeroE` (`AX = z.ptr`) -/
theorem zeroP {impl : List Amd64.Segment} (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s)
    (hk : 4320 ≤ stk) (hA : 72 ≤ A) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hv0 : natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm = 0) (S : State) (hpc : S.rip = BitVec.ofNat 64 zeroE)
    (esp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x70)) (e0 : S.regs 0 = BitVec.ofNat 64 zp)
    (e1 : S.regs 1 = BitVec.ofNat 64 zc) (e14 : S.regs 14 = s.regs 14) (efs : S.fsBase = s.fsBase)
    (ex : S.xmm 15 = s.xmm 15) (edf : S.df = s.df)
    (hm : S.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := epi_of hP hk hA hra
  have hsp : 0x70 ≤ (s.regs 4).toNat := by
    have := hP.1.1.2.1.1; simp only [regSP] at this; omega
  rw [← hm] at q2 q3 q4
  rw [hv0]
  exact zeroR hpc esp q1 q2 q3 q4 q5 fun s' hE a0 a3 a1 am => postE hP hk hA hE e14 efs ex edf (zs := [])
    (by rw [List.append_nil]; exact w0_own (by omega) hA hsp) (fun r hr => by simp at hr) (Nat.zero_le _)
    (by simp [natVal]) (Or.inl rfl) (am.trans hm) (a0.trans e0) (by rw [a3]) (a1.trans e1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`return z[:0]`** from `zero2` (`R13 = z.ptr`) -/
theorem zero2P {impl : List Amd64.Segment} (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s)
    (hk : 4320 ≤ stk) (hA : 72 ≤ A) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hv0 : natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm = 0) (S : State) (hpc : S.rip = BitVec.ofNat 64 zero2)
    (esp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x70)) (e13 : S.regs 13 = BitVec.ofNat 64 zp)
    (e1 : S.regs 1 = BitVec.ofNat 64 zc) (e14 : S.regs 14 = s.regs 14) (efs : S.fsBase = s.fsBase)
    (ex : S.xmm 15 = s.xmm 15) (edf : S.df = s.df)
    (hm : S.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := epi_of hP hk hA hra
  have hsp : 0x70 ≤ (s.regs 4).toNat := by
    have := hP.1.1.2.1.1; simp only [regSP] at this; omega
  rw [← hm] at q2 q3 q4
  rw [hv0]
  exact zero2R hpc esp q1 q2 q3 q4 q5 fun s' hE a0 a3 a1 am => postE hP hk hA hE e14 efs ex edf (zs := [])
    (by rw [List.append_nil]; exact w0_own (by omega) hA hsp) (fun r hr => by simp at hr) (Nat.zero_le _)
    (by simp [natVal]) (Or.inl rfl) (am.trans hm) (a0.trans e13) (by rw [a3]) (a1.trans e1)

end

end FvModexp.Amd64.P2D
