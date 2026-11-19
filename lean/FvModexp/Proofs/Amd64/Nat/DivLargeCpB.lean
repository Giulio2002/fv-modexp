import FvModexp.Proofs.Amd64.Nat.DivLargeCpF
import FvModexp.Proofs.Amd64.Nat.DivLargeCpA

set_option autoImplicit false

/-!
# `divLarge` (amd64): copy path after `copy(v, vIn)` (`AtV`, `fn + 0x277`): `copy(u[:len uIn], uIn)` (natdiv.go:611;
the `memmove` at `+0x2e0` is skipped when `u`'s array is `uIn`'s: `CMPQ BX, R8; JE +0x327`), `u[len uIn] = 0`
(natdiv.go:612, `+0x330`) → the alias test (`aliasPt = fn + 0x452`, `AtAl` with `shift = 0`).
Port of `Arm64/Nat/DivLargeCpB.lean` + `DivLargeCpE.lean`.

Reloads (`SP' = RSP - 304`): `AX = [SP'+0xd0] = t`, `CX = [SP'+0x98] = vl`, `DX = [SP'+0x80] = shift = 0`,
`SI = [SP'+0x78] = C`, `DI = [SP'+0x68] = il + 1`, `R8 = [SP'+0xc8] = P`, `R11 = [RSP+40] = vl`, `R12 = [SP'+0x90] = vl`,
`R13 = [RSP+16] = il`; `CMPQ R13, SI; JA panic` (not taken: `il < C`); `BX = [RSP+8] = ip`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivLarge

/-- the join of both copy branches (`fn + 0x327`, `CMPQ R13, DI`) -/
abbrev cpJoin : Nat := segAddr Extracted.program fn + 0x327

/-- `copy(u, uIn)`'s `memmove` return (`fn + 0x2e5`) -/
abbrev cpRet2 : Nat := segAddr Extracted.program fn + 0x2e5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`u[il] = 0` → the alias test** (`cpJoin` → `aliasPt`): `CMPQ R13 = il, DI = il + 1; JAE` not taken, the store,
`JMP aliasPt`; then `cp_fin` -/
theorem cpE (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {V : State}
    (hV : AtV R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C V)
    (hclz : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0)
    {m4 : Memory} {cs : List (Nat × Nat)}
    (hMF2 : MemFrame V.mem m4 (R.rt ++ cs ++ [(P, P + 8 * il)]))
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 41272 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 209)
    (hLF2 : LiveFrame V.mem m4 Lk [(P, P + 8 * il)])
    (hinv4 : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk m4))
    (hval : natVal m4 P il = natVal s.mem ip il) (hreg4 : m4.regions = s.mem.regions)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 cpJoin) (hsp : X.regs 4 = s.regs 4 - 304#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hx : X.xmm 15 = 0#128) (hdf : X.df = false)
    (h0 : X.regs 0 = BitVec.ofNat 64 t) (h1 : X.regs 1 = BitVec.ofNat 64 vl) (h2 : X.regs 2 = BitVec.ofNat 64 0)
    (h6 : X.regs 6 = BitVec.ofNat 64 C) (h7 : X.regs 7 = BitVec.ofNat 64 (il + 1))
    (h8 : X.regs 8 = BitVec.ofNat 64 P) (h11 : X.regs 11 = BitVec.ofNat 64 vl) (h12 : X.regs 12 = BitVec.ofNat 64 vl)
    (h13 : X.regs 13 = BitVec.ofNat 64 il) (hm : X.mem = m4) (Q : State → Prop)
    (k : ∀ T, AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C 0 T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) X Q := by
  have hl := hE.lay
  have hil9 := hl.il9
  have hU := hV.ua
  have hcap := hU.cap; have hp48 := hU.p48; have hc40 := hU.c40
  obtain ⟨hmU, hUA, hvv, hvt, huv⟩ := cp_fin hE hV hclz hMF2 hcs hLF2 hinv4 hval
  have hacc : m4.accessible (P + 8 * il) 8 true = true := by
    rw [hMF2.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hU.pacc (by omega) (by omega)
  have hPa : (P + 8 * il) % 2 ^ 64 = P + 8 * il := Nat.mod_eq_of_lt (by omega)
  janus64_run [hm, hPa] until [aliasPt]
  rw [show P + il * 8 = P + 8 * il by omega]
  exact k _ ⟨rfl, hsp, h5, h14, hfs, hx, rfl, h0, h1, h2, h6, h7, h8, h11, h12, hmU, hUA, hV.ext2, hV.bud2, by omega,
    hvv, hvt, huv, by simp only [Janus.Arm64.Memory.regions_writeLE]; exact hreg4⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
/-- **the copy path after `copy(v, vIn)`** (`AtV` → `AtAl`, `shift = 0`): `copy(u[:il], uIn)` (`memmove`, skipped when
`P = uIn`), `u[il] = 0` -/
theorem cpB (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (V : State)
    (hV : AtV R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C V)
    (hclz : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0) (Q : State → Prop)
    (k : ∀ T, AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C 0 T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) V Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hil9 := hl.il9; have hvil := hl.vil
  have hU := hV.ua
  have hc40 := hU.c40; have hcap := hU.cap; have hp48 := hU.p48
  have hMU := hV.mem
  have hM := hMU.mem
  have q1 := hM.vt; have q2 := hM.vn2; have q3 := hMU.ssh; have q4 := hMU.sC; have q5 := hMU.sL
  have q6 := hMU.sP; have q7 := hM.vlS; have q8 := hM.vn1; have q9 := hM.ilS; have q10 := hM.ipS
  have hpc := hV.pc; have hsp := hV.sp; have h5 := hV.r5; have h14 := hV.r14; have hfs := hV.fs
  have hx := hV.x15; have hdf := hV.df
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hE.pre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  have hSacc : ∀ a n v, V.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : V.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hSacc]; exact hw
  have hgacc : V.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hSacc]; exact hg2
  by_cases hPi : P = ip
  · subst hPi
    have hPP : (BitVec.ofNat 64 P = BitVec.ofNat 64 P) = True := eq_self _
    janus64_run [q1, q2, q3, q4, q5, q6, q7, q8, q9, q10] until [cpJoin]
    have hval : natVal V.mem P il = natVal s.mem P il := by
      unfold natVal; exact hV.is _ _ (Nat.le_refl _) (Nat.le_refl _)
    refine cpE impl R b L c zp zc st up uc P il vp vl s t w1 c1 L1 b1 Lk bk P C hE hV hclz (m4 := V.mem) (cs := [])
      ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩ (fun r hr => by simp at hr) ⟨fun _ _ _ _ => rfl⟩ hM.inv hval hV.reg _ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Q k
    all_goals (try janus64_simp)
    all_goals (first | exact hsp | exact h5 | exact h14 | exact hfs | exact hx | exact hdf | rfl)
  · have hap : Apart P (8 * C) ip (8 * il) := hU.pi.resolve_left hPi
    unfold Apart at hap
    have hiw := hl.iw; have hi48 := hl.i48; have hpw := hU.pw
    have hne : (BitVec.ofNat 64 ip = BitVec.ofNat 64 P) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have hne1 : ((18446744073709551616 - P + ip) % 18446744073709551616 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; omega
    have hne2 : ((18446744073709551616 - ip + P) % 18446744073709551616 = 0) = False := by
      simp only [eq_iff_iff, iff_false]; intro e; omega
    have hsh : BitVec.ofNat 64 il <<< 3 = BitVec.ofNat 64 (8 * il) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft]; simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
    have hok : R.ok (cA "runtime.memmove") [P, ip, 8 * il] := hE.pre.sv.2.1 _ _ _ (by omega)
    have hLs := lsep_of hE hV.ext2
    have hph : Held R Lk P (8 * il) := hU.pheld.sub (by omega) (by omega)
    have hph' : InRanges P (8 * il) Lk ∨ Outside P (8 * il) R.rt := hph
    have hdacc : V.mem.accessible P (8 * il) true = true :=
      Janus.Arm64.Memory.accessible_mono _ hU.pacc (by omega) (by omega)
    have hsacc : V.mem.accessible ip (8 * il) false = true := by rw [hSacc]; exact hE.pre.io.2.1
    have hinv := hM.inv
    have hga := hE.pre.ce.2.2.2.2.2.1
    unfold Apart at hga
    obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
    have htS : V.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
    have hgrd := hMU.grd
    janus64_run [q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, hne, hne1, hne2, hsh, htS, ite_self] until [cpRet2]
      calls [hmv Lk bk]
    rename_i m _ _ hF2 hLF2 hinv2 hcp
    generalize hG : Janus.Arm64.Memory.writeLE V.mem ((s.regs 4).toNat - 312) 8 6220805 = M1 at hF2 hLF2 hcp
    have hW0 : MemFrame V.mem M1 [((s.regs 4).toNat - 312, (s.regs 4).toNat - 312 + 8)] := by
      rw [← hG]; janus_frame
    have rd : ∀ a, (s.regs 4).toNat - 280 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 → m.readLE a 8 = V.mem.readLE a 8 := by
      intro a h1 h2
      rw [hF2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩),
        hW0.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    have r1 := (rd _ (by omega) (by omega)).trans q1; have r2 := (rd _ (by omega) (by omega)).trans q2
    have r3 := (rd _ (by omega) (by omega)).trans q3; have r4 := (rd _ (by omega) (by omega)).trans q4
    have r5 := (rd _ (by omega) (by omega)).trans q5; have r6 := (rd _ (by omega) (by omega)).trans q6
    have r7 := (rd _ (by omega) (by omega)).trans q7; have r8 := (rd _ (by omega) (by omega)).trans q8
    have r9 := (rd _ (by omega) (by omega)).trans q9
    have hMF2 : MemFrame V.mem m (R.rt ++ ([((s.regs 4).toNat - 312, (s.regs 4).toNat - 312 + 8),
        ((s.regs 4).toNat - 312 - 4096, (s.regs 4).toNat - 312),
        ((s.regs 4).toNat - 312 + 8, (s.regs 4).toNat - 312 + 8 + 24)]) ++ [(P, P + 8 * il)]) :=
      (mfTrans hW0 hF2).mono fun a n ho => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨ho.1.2.1, ⟨ho.1.1, ho.1.2.2.1, ho.1.2.2.2⟩, ho.2⟩
    have hLF2' : LiveFrame V.mem m Lk [(P, P + 8 * il)] := ⟨fun a n hin ho => by
      rw [hLF2.readLE a n hin ho, ← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_]
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; omega⟩
    have hval : natVal m P il = natVal s.mem ip il := by
      unfold natVal
      rw [FvModexp.Expmc.readLE_of_copied hcp, ← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hV.is _ _ (Nat.le_refl _) (Nat.le_refl _)
    have hreg4 : m.regions = s.mem.regions := by
      rename_i hrg1; rw [hrg1]; exact hV.reg
    have hra : M1.readLE ((s.regs 4).toNat - 312) 8 = 6220805 := by
      rw [← hG, Janus.Arm64.Memory.readLE_writeLE_self]
    janus64_run [hra, r1, r2, r3, r4, r5, r6, r7, r8, r9] until [cpJoin]
    refine cpE impl R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C hE hV hclz hMF2
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only <;> omega) hLF2' hinv2 hval hreg4 _ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Q k
    all_goals (try janus64_simp)
    all_goals (first | exact hsp | exact h5 | exact h14 | exact hfs | exact hx | exact hdf | rfl)

end FvModexp.Amd64.DivLarge
