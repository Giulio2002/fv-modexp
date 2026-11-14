import FvModexp.Proofs.Amd64.NatQ.DrsDG
import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsD7.lean)
# `divRecursiveStep` (amd64), end of an iteration: `stk.restore(mark)` and the back edge (nat.go:315, natdiv.go:793)

`d7`: from `G` at `0x5f00ad` (`rD6`): `DI = stk`, `DX = cap`, `R9 = mark`; `CMPQ DX, R9; JAE 0x5efa3b`;
`MOVQ R9, 8(DI)` (`len := mark`); `AX = t0`, `CX = BX = B + 1`, `DX = j - B` → the loop head `0x5efa5f` with `H (j - B)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem apSD {a n b k a' n' : Nat} (h : Apart a n b k) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Apart a' n' b k := by
  unfold Apart at h ⊢; omega

theorem bud_next {lo K bk j B X : Nat} (hB : 0 < B) (hj : B < j) (h : lo + (j / B) * K + X ≤ bk) :
    lo + ((j - B) / B + 1) * K + X ≤ bk := by
  have e : j / B = (j - B) / B + 1 := by rw [← Nat.add_div_right _ hB, Nat.sub_add_cancel (by omega)]
  rw [← e]; exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d7 (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (Q : State → Prop) (S : State) (hpc : S.rip = BitVec.ofNat 64 rD6)
    (hG : G R c s Lk bk S j Z U)
    (k : ∀ S', H R c s Lk bk S' (j - c.vl / 2) → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hcr := hG.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hqs := hpre.sq.1; have hus := hpre.su.1; have hvs := hpre.sv2.1
  have hsto : Outside c.st 24 (win s c.W 96) := hpre.sti.2.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsp := hG.sp; have h5 := hG.r5; have h14 := hG.r14; have hfs := hG.fs; have hdf := hG.df
  have hx15 := hG.x15
  have hspT : (S.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hG.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hlc := hG.ev.sok.2.2.2.2.2.1
  have hlen := hG.fp.len
  have hc40 := hG.ev.sok.2.2.2.2.2.2
  have hst48 := hG.ev.sok.2.2.2.1
  have hsta := hG.ev.sok.2.2.1
  have hl1 : c.l1 s ≤ stCap S.mem c.st := by simp only [Cx.l1, StackNat.rnd] at hlen hlc ⊢; omega
  have hl64 : c.l1 s < 2 ^ 64 := by omega
  obtain ⟨K, hK⟩ : ∃ K, S.mem.readLE (c.st + 16) 8 = K := ⟨_, rfl⟩
  have hK' : stCap S.mem c.st = K := hK
  have hKb : (BitVec.ofNat 64 K < BitVec.ofNat 64 (c.l1 s)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt (by omega)]; omega
  have r1 := hG.sl.s4; have r2 := hG.mrk; have r3 := hG.sl.q0p; have r4 := hG.sl.q0l; have r5 := hG.sl.q0c
  have r6 := hG.sj
  have hB : Box (G R c s Lk bk S j Z U) := ⟨hG⟩
  clear hG hpre
  have hsto' := hsto
  simp only [win, outside_cons, outside_nil, and_true] at hsto'
  janus64_run [r1, r2, r3, r4, r5, r6, hK, hKb] until [head]
  -- the state after the store
  have hG := hB.1
  have hF : MemFrame S.mem (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) [(c.st + 8, c.st + 16)] :=
    MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (Nat.le_refl _)
  have rd : ∀ x n, Apart x n c.st 24 → (S.mem.writeLE (c.st + 8) 8 (c.l1 s)).readLE x n = S.mem.readLE x n :=
    fun x n h => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at h; omega)
  have hfo : FixOut s [(c.st + 8, c.st + 16)] := by
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have hli := li_next hcr hG.li hG.jB
  rw [← hG.zk, ← hG.uk] at hli
  have kz : Asm.limbs (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) c.qp c.ql = Asm.limbs S.mem c.qp c.ql :=
    limbs_congr (rd _ _ hqs)
  have ku : Asm.limbs (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) c.up c.u1 = Asm.limbs S.mem c.up c.u1 :=
    limbs_congr (rd _ _ (apSD hus (Nat.le_refl _) (by have := hcr.u1ul; omega)))
  have eCw : stCap (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) c.st = stCap S.mem c.st :=
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (Or.inr (by omega))
  refine k _ ⟨rfl, ?sp, ?r5, ?r14, hfs, (by dsimp only), ?x15, ?a0, ?a3, ?a1, ?a2, hcr, Ev.restore hG.ev _ hl1 hl64,
    Fp.restore hG.fl hl64, hG.sl.frame hF hfo, by rw [kz, ku]; exact hli, by rw [rd _ _ hvs]; exact hG.vk,
    by rw [rd _ _ (apSD hus (by omega) (by have := hcr.u1ul; omega))]; exact hG.utl,
    bud_cap eCw (bud_next (by omega) hG.jB hG.bud)⟩
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case sp => exact hsp
  case r5 => exact h5
  case r14 => exact h14
  case x15 => exact hx15

end FvModexp.Amd64.Q.DivRec
