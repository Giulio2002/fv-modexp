import FvModexp.Proofs.Amd64.NatQ.KSqrRel

/-!
# [amd64 port (divmc s38) of the Q-form Arm64/NatQ/KSqrCall.lean — TIGHT COSTS] `karatsubaSqr` (amd64): an inner `nat.sqr` call through the induction hypothesis of the squaring SCC

`ks_sqcall`: at the entry of `nat.sqr` (`0x5f0fe0`), called from `karatsubaSqr`'s frame (`SP - 320`) with `KM`, the
operand facts of `KM.sqrPre` and a smaller measure, the call returns with `Kept` and `SPost` (continuation form).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

theorem tN' {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
theorem ks_sqcall (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) (ih : ∀ a, IH impl R H (2 * n) (false, a))
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 0x5f0fe0) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 320)
    (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M) (hfs : S1.fsBase = s.fsBase)
    (hra : S1.mem.readLE (S1.regs 4).toNat 8 < 2 ^ 47) (hx15 : S1.xmm 15 = 0#128) (hdf : S1.df = false)
    {zp' zl' zc' xp' xl' xc' : Nat} (b0 : zp' < 2 ^ 64) (b1 : zl' < 2 ^ 64) (b2 : zc' < 2 ^ 64) (b3 : st < 2 ^ 64)
    (b4 : xp' < 2 ^ 64) (b5 : xl' < 2 ^ 64) (b6 : xc' < 2 ^ 64)
    (r0 : S1.regs 0 = BitVec.ofNat 64 zp') (r1 : S1.regs 3 = BitVec.ofNat 64 zl')
    (r2 : S1.regs 1 = BitVec.ofNat 64 zc') (r3 : S1.regs 7 = BitVec.ofNat 64 st)
    (r4 : S1.regs 6 = BitVec.ofNat 64 xp') (r5 : S1.regs 8 = BitVec.ofNat 64 xl')
    (r6 : S1.regs 9 = BitVec.ofNat 64 xc')
    (hxl : xl' ≤ kn2 n) (hxc : xl' ≤ xc') (hxc40 : xc' < 2 ^ 40)
    (hxacc : M.accessible xp' (8 * xl') false = true)
    (hxh : 0 < xc' → Held R Lk xp' (8 * xc') ∧ xp' + 8 * xc' ≤ 2 ^ 48)
    (hxw : 0 < xl' → Outside xp' (8 * xl') (win s W 48))
    (hzc40 : zc' < 2 ^ 40) (hzl : NatLive M R Lk zp' zc') (hzw : Outside zp' (8 * zc') (win s W 48))
    (hzg : 0 < zc' → Apart zp' (8 * zc') (guard s) 8 ∧ Apart zp' (8 * zc') (tls s) 8 ∧ StkSep M st zp' (8 * zc'))
    (hal : (zp' = xp' ∧ zc' = xc') ∨ (0 < zc' → 0 < xl' → Apart zp' (8 * zc') xp' (8 * xl')))
    (hxs : 0 < xl' → StkSep M st xp' (8 * xl')) (hcost : sqrCQ xl' + stkR H M st ≤ bk)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.rip = retAddrOf S1 → s2.mem.regions = M.regions → Kept S1 s2 →
      SPost R bk H Lk (W - 320) zp' zc' st xp' xl' xc' S1 s2 → ReachesRet (LibSqr.program.link impl) ret s2 Q) :
    ReachesRet (LibSqr.program.link impl) ret S1 Q := by
  have hW := h.lay.1
  have h80 := h.lay.2.2.2.2.1
  have hP := h.sqrPre hsp hg hm hxl hxc hxc40 hxacc hxh hxw hzc40 hzl hzw hzg hal hxs hcost hfs
  refine ReachesRet.call_regions (ih ⟨bk, Lk, W - 320, BitVec.ofNat 64 zp', BitVec.ofNat 64 zl',
    BitVec.ofNat 64 zc', BitVec.ofNat 64 st, BitVec.ofNat 64 xp', BitVec.ofNat 64 xl', BitVec.ofNat 64 xc'⟩)
    (by rw [hpc]; rfl) ⟨⟨⟨hra, hx15, hdf, r0, r1, r2, r3, r4, r5, r6⟩, ?_⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · show SPre R bk H Lk (W - 320) (BitVec.ofNat 64 zp').toNat (BitVec.ofNat 64 zc').toNat (BitVec.ofNat 64 st).toNat
      (BitVec.ofNat 64 xp').toNat (BitVec.ofNat 64 xl').toNat (BitVec.ofNat 64 xc').toNat S1
    rw [tN' b0, tN' b2, tN' b3, tN' b4, tN' b5, tN' b6]; exact hP
  · show 2 * (BitVec.ofNat 64 xl').toNat + 1 < 2 * n
    have := hxl; simp only [kn2] at this; rw [tN' b5]; omega
  · obtain ⟨hk, hq⟩ := hq
    have hq' : SPost R bk H Lk (W - 320) (BitVec.ofNat 64 zp').toNat (BitVec.ofNat 64 zc').toNat
        (BitVec.ofNat 64 st).toNat (BitVec.ofNat 64 xp').toNat (BitVec.ofNat 64 xl').toNat (BitVec.ofNat 64 xc').toNat
        S1 s2 := hq
    rw [tN' b0, tN' b2, tN' b3, tN' b4, tN' b5, tN' b6] at hq'
    exact hK s2 hr (by rw [hreg, hm]) hk hq'

end FvModexp.Amd64.Q.NatSqr
