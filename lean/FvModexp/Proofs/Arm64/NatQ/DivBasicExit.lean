import FvModexp.Proofs.Arm64.NatQ.DivBasicEnd
import FvModexp.Proofs.Arm64.NatQ.DivBasicCallees

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivBasicExit.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): the loop exit (`TBNZ $63, R1` taken) through the deferred closure to the return

`+0xcc TBNZ → +0x32c MOVB ZR, 103(RSP); R26 = 224(RSP); R0 = (R26); CALL (R0)` (`deferwrap1` = `stk.restore`,
`dsum`) `; MOVD -8(RSP), R29; MOVD.P 240(RSP), R30; RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivBasic
open FvModexp.Arm64.DivBasic
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem fin (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (r1 ujn : Nat)
    (hH : Hd R b H L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S r1 ujn)
    (h63 : (BitVec.ofNat 64 r1).getLsbD 63 = true)
    (hq : vl ≤ ul → natVal S.mem qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl)
    (hu : natVal S.mem up ul = natVal s.mem up ul % natVal s.mem vp vl) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S (RQ R b H L qp ql st up ul vp vl s) := by
  obtain ⟨hpc, hsp, h28, h29, h18, -, hr1, -, hE, hM⟩ := hH
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hspa := hl.spa; have hsw := hl.sw
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, hga, hgr, -, -⟩ := hpre.ce
  obtain ⟨hst8, -, hstacc, hst48, -, -, -⟩ := hpre.stok
  have hc1 := hE.c1len
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have hsacc : S.mem.accessible st 24 true = true := by rw [hMacc]; exact hstacc
  have m1 := hM.lr; have m2 := hM.fp; have mdp := hM.dp; have mdf : S.mem.readLE (s.sp.toNat - 40) 8 = 1811280 := hM.dfn; have mcap := hM.hcap
  have f8 : S.mem.readLE (s.sp.toNat - 40 + 8) 8 = st := by
    rw [show s.sp.toNat - 40 + 8 = s.sp.toNat - 32 by omega]; exact hM.dst
  have f16 : S.mem.readLE (s.sp.toNat - 40 + 16) 8 = stLen s.mem st := by
    rw [show s.sp.toNat - 40 + 16 = s.sp.toNat - 24 by omega]; exact hM.dn
  have hgacc : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hMacc]; exact hg2
  have hqn : qn ql ul vl ≤ ql := by unfold qn; split <;> omega
  have eg : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    have hstg := hpre.stg; have hfr := hpre.stgf; simp only [freeP, freeN] at hfr; unfold Apart at hstg hfr hga
    have := hl.qg; have := hl.ug; have := hl.tg; have := hl.gw
    refine hM.fr.readLE _ _ ?_
    simp only [winA, wsL, stkWs, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨⟨hgr, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> omega
  have hD : Summary (LibDivBasic.program.link impl) 1811280 Restore.Pre Restore.Post := dsum impl
  clear hpre
  janus_run [hr1, h63, m1, m2, mdp, mdf, mcap, f8, f16, eg] calls [hD]
  rename_i hpcC hspC h18C h28C h29C hlen hFF _
  rw [show s.sp.toNat - 240 - 24 = s.sp.toNat - 264 by omega, show s.sp.toNat - 240 - 8 = s.sp.toNat - 248 by omega]
    at hFF
  have hFE : MemFrame S.mem (S.mem.writeLE (s.sp.toNat - 137) 1 0) [(s.sp.toNat - 137, s.sp.toNat - 136)] :=
    MemFrame.of_writeLE _ _ (List.mem_singleton_self _) (Nat.le_refl _) (by omega)
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, post_fin hE hM hq hu hFE hFF hlen _ rfl⟩
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at h28C ⊢; rw [h28C, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at h18C ⊢; rw [h18C, h18]

end FvModexp.Arm64.Q.DivBasic
