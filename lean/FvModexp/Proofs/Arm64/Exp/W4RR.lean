import FvModexp.Proofs.Arm64.Exp.W4OneRet2
import FvModexp.Proofs.Arm64.Exp.W4ZcDefs

/-!
# window-4 prologue (arm64): `RR` gets exactly `numWords` words (nat.go:1398-1403), from the return of
`stk.nat(2n).div(stk, RR, zz, m)` (`divRet` = fn+0x41c) to `oneJ`

`len(RR) ≥ n` (then `= n`, `RR < m`): `RR` is the remainder. `len(RR) < n`: `zz = zz.make(n)` reuses `zz` (its
capacity is `≥ 2n + 1`, the `makeslice` branches are refuted), `copy(zz, RR)` (memmove), `RR = zz`; the words
`zz[len RR : n]` are still zero from `zz = 2^(128 n)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- return of `nat.div` (RR) -/
abbrev divRet : Nat := 1799564

/-- the frame words `divRet → oneJ` writes (memmove window, spills) -/
@[reducible] def rw4 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 168, sp + 176), (sp + 256, sp + 272), (sp + 304, sp + 312),
    (sp + 400, sp + 408), (sp + 832, sp + 840), (sp + 888, sp + 896)]

/-- the facts at `oneJ` -/
@[reducible] def RRPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M M' : Memory)
    (rrp rrc : Nat) : Prop :=
  MemFrame M M' (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ LiveFrame M M' L [(zzp, zzp + 8 * n)] ∧
  R.inv b L g (view R.rt L M') ∧ M'.regions = M.regions ∧
  M'.readLE (sp + 832) 8 = rrp ∧ M'.readLE (sp + 264) 8 = rrc ∧ M'.readLE (sp + 256) 8 = n ∧
  M'.readLE (sp + 400) 8 = zzp ∧ M'.readLE (sp + 168) 8 = zzc ∧ M'.readLE rrp (8 * n) = M.readLE rp (8 * rl) ∧
  ((rrp = rp ∧ rrc = rc ∧ rl = n) ∨ (rrp = zzp ∧ rrc = zzc ∧ rl < n))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem rrA (impl : List Segment) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret)
    (Q : Outcome → Prop) (R : RtInv) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn16 : n ≤ 2 ^ 16) (hrl : n ≤ rl) (hrl' : rl < 2 ^ 40) (hrc : rc < 2 ^ 40) (hrp : rp < 2 ^ 64)
    (hrln : rl ≤ n) (hra : Apart rp (8 * rl) (sp - 4288) (4288 + 1040)) (b : Nat) (hinv : R.inv b L g (view R.rt L M))
    (hzzp : zzp < 2 ^ 64) (hzzc : zzc < 2 ^ 40)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 rp) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KR : ∀ (S' : State) (M' : Memory) (rrp rrc : Nat), S'.pc = BitVec.ofNat 64 oneJ → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 n → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 →
      S'.mem = M' → RRPost R b L g sp n rp rl rc zzp zzc M M' rrp rrc →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have u := hra; unfold Apart at u
  janus_run [r1024, r168, r400] until [oneJ]
  refine KR _ _ rp rc ?_ ?_ ?_ ?_ ?_ ?_ rfl ⟨?_, ?_, ?_, by simp only [Memory.regions_writeLE], ?_, ?_, ?_, ?_, ?_, ?_,
    Or.inl ⟨rfl, rfl, by omega⟩⟩
  all_goals first | (janus_simp; done) | skip
  · repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 168, sp + 176)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 400, sp + 408)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 832, sp + 840)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 256, sp + 272)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  · repeat (refine LiveFrame.writeLE ?_ _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega)))
    exact LiveFrame.refl _ _ _
  · repeat (refine inv_store_out ?_ (hwrt.of_sub (by omega) (by omega)))
    exact hinv
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.reducePow]
  all_goals first | omega | (rw [show rl = n by omega])

end FvModexp.Arm64.W4Pro
