import FvModexp.Proofs.Amd64.NatQ.DivLargeShRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeShC.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `shift ≠ 0`, after the second `lshVU` (`AtS2`, `fn + 0x3e6`): `u[il] = carry` → the alias test

`XORPS X15, X15; MOVQ FS:-8, R14`; `AX = [RSP + 16] = il`, `R8 = [SP' + 0x68] = il + 1`; `CMPQ AX, R8; JAE panic`
(not taken); `DX = [SP' + 0x38]` (the carry), `SI = [SP' + 0xc8] = P`; `MOVQ DX, (SI)(AX*8)` (`+0x416`); reloads
`AX = t`, `CX = vl`, `DX = shift`, `SI = C`, `DI = il + 1`, `R8 = P`, `R11 = R12 = vl` → `aliasPt` (`AtAl`).
Port of `Arm64/Nat/DivLargeShC.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `u[il] := carry` (pure): `MemU`, `UArr`, `u = uIn · 2^sh` -/
theorem sh_store {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C sh : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtS2 R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S) :
    MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C sh
        (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8)) ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C
        (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8)) ∧
      natVal (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8)) t vl = natVal s.mem vp vl * 2 ^ sh ∧
      2 ^ 63 ≤ (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8)).readLE (t + 8 * (vl - 1)) 8 ∧
      natVal (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8)) P (il + 1) =
        natVal s.mem ip il * 2 ^ sh := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hU := hS.ua
  have hcap := hU.cap; have hp48 := hU.p48
  have hpvt := hU.pvt
  unfold Apart at hpvt
  have hLL : ∀ a n, InRanges a n L → InRanges a n Lk := fun a n h => hS.ext2.inRanges_old (hE.ext.inRanges_old h)
  have hW : MemFrame S.mem (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8))
      [(P + 8 * il, P + 8 * il + 8)] := by janus_frame
  have hinv5 : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk
      (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8))) :=
    inv_store_held hS.mem.mem.inv (hU.pheld.sub (by omega) (by omega))
  obtain ⟨hJ, hUJ⟩ := MemU.call hE hS.mem hU (cs := []) (ext := [(P + 8 * il, P + 8 * il + 8)])
    (hW.mono fun a n h => by simp only [outside_append] at h; exact h.2) (fun r hr => by simp at hr)
    (fun a n h => by simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega)
    ⟨fun a n _ h => hW.readLE a n h⟩ hLL hinv5
  have hvt : ∀ o n, o + n ≤ 8 * vl →
      (S.mem.writeLE (P + 8 * il) 8 (S.mem.readLE ((s.regs 4).toNat - 248) 8)).readLE (t + o) n =
        S.mem.readLE (t + o) n := fun o n h =>
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨hJ, hUJ, ?_, ?_, ?_⟩
  · have := hvt 0 (8 * vl) (by omega)
    simp only [Nat.add_zero] at this
    unfold natVal; rw [this]; exact hS.vval
  · rw [hvt _ _ (by omega)]; exact hS.vtop
  · rw [natVal_store_top _ _ _ _ (Janus.Arm64.Memory.readLE_lt _ _ _), hS.uval, hS.cy]
    exact Nat.mod_add_div _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem shC (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtS2 R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S) (Q : State → Prop)
    (k : ∀ T, AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hMU := hS.mem
  have hM := hMU.mem
  have m1 := hM.ilS; have m2 := hMU.sL; have m3 := hMU.sP; have m4 := hM.vt; have m5 := hM.vn2
  have m6 := hMU.ssh; have m7 := hMU.sC; have m8 := hM.vlS; have m9 := hM.vn1
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have hfs := hS.fs; have hdf := hS.df
  have hU := hS.ua
  have hcap := hU.cap; have hp48 := hU.p48; have hc40 := hU.c40
  obtain ⟨hJ, hUJ, hvv, hvt, huv⟩ := sh_store hE hS
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hE.pre.ce
  simp only [regSP] at hb' ha hw
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    rw [hM.fr.accessible]; exact hw
  have htacc : S.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hM.fr.accessible]; exact htr
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
  have hacc : S.mem.accessible (P + 8 * il) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hU.pacc (by omega) (by omega)
  have hPa : (P + 8 * il) % 2 ^ 64 = P + 8 * il := Nat.mod_eq_of_lt (by omega)
  janus64_run [m1, m2, m3, m4, m5, m6, m7, m8, m9, htS, hfs, hPa] until [aliasPt]
  rw [show P + il * 8 = P + 8 * il by omega]
  have hpw := hU.pw
  refine k _ ⟨?pc, ?sp, ?r5, ?r14, ?fs, ?x15, ?df, ?r0, ?r1, ?r2, ?r6, ?r7, ?r8, ?r11, ?r12, hJ, hUJ, hS.ext2, hS.bud2,
    hS.sh63, hvv, hvt, huv, ?reg⟩
  all_goals (try janus64_simp)
  all_goals (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, m1, m2, m3, m4, m5, m6, m7,
    m8, m9, htS, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  case reg => exact hS.reg

end FvModexp.Amd64.Q.DivLarge
