import FvModexp.Proofs.Amd64.NatQ.DivLargeShRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeShA.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `shift ≠ 0` (natdiv.go:614), from `joinU` through `lshVU(v, vIn, shift)` → `AtS1`

`+0x216`: the `joinU` stores (`C`, `il + 1`, `P`, `shift = clz vIn[n-1]` at `RSP - 184, - 200, - 104, - 176`);
`TESTQ DX; JNE +0x33d` taken; ABI0 arguments at `SP' + 0 … + 0x30` (`SP' = RSP - 304`): `z = (t, vl, vl)`,
`x = (vp, vl, [RSP + 48])`, `s = shift`; `CALL lshVU.abi0` (`+0x377`) → return `+0x37c` (`AtS1`).
Port of `Arm64/Nat/DivLargeShA.lean` (the callee summary is applied by `janus64_run calls`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

/-- `lshVU`'s postcondition with the frame words of the call state known (copy of `Lsh.lshQ`) -/
theorem lshQ {C : State} {m : Janus.Arm64.Memory} {z n x r : Nat}
    (hz : C.mem.readLE ((C.regs 4).toNat + 8) 8 = z)
    (hn : C.mem.readLE ((C.regs 4).toNat + 16) 8 = n) (hx : C.mem.readLE ((C.regs 4).toNat + 32) 8 = x)
    (hs : C.mem.readLE ((C.regs 4).toNat + 56) 8 = r) (h : LshVUSum.Q C m) :
    natVal m z n = (natVal C.mem x n * 2 ^ r) % 2 ^ (64 * n) ∧
      m.readLE ((C.regs 4).toNat + 64) 8 = (natVal C.mem x n * 2 ^ r) / 2 ^ (64 * n) ∧
      MemFrame C.mem m [(z, z + 8 * n), ((C.regs 4).toNat + 64, (C.regs 4).toNat + 72)] := by
  unfold LshVUSum.Q at h
  rw [hz, hn, hx, hs] at h
  exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- after `lshVU(v, vIn, shift)` (pure): the `joinU` + argument stores (`M1`, inside `scrJ`), `lshVU`'s write set
(`v` at `t`, the result word `RSP - 248`) → `MemU`, `UArr`, `v = vIn · 2^sh` normalised, `uIn` unchanged -/
theorem sh1_post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtU R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C S)
    (hgrd : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    {sh : Nat} (hsh : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh)
    {M1 w : Janus.Arm64.Memory} (hfJ : MemFrame S.mem M1 (scrJ s))
    (h1 : M1.readLE ((s.regs 4).toNat - 184) 8 = C) (h2 : M1.readLE ((s.regs 4).toNat - 200) 8 = il + 1)
    (h3 : M1.readLE ((s.regs 4).toNat - 104) 8 = P) (h4 : M1.readLE ((s.regs 4).toNat - 176) 8 = sh)
    (hq1 : natVal w t vl = natVal M1 vp vl * 2 ^ sh % 2 ^ (64 * vl))
    (hq3 : MemFrame M1 w [(t, t + 8 * vl), ((s.regs 4).toNat - 312 + 64, (s.regs 4).toNat - 312 + 72)])
    (hinv1 : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk w)) :
    MemU R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk P C sh w ∧
      UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C w ∧
      natVal w t vl = natVal s.mem vp vl * 2 ^ sh ∧ 2 ^ 63 ≤ w.readLE (t + 8 * (vl - 1)) 8 ∧
      (∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → w.readLE a n = s.mem.readLE a n) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hM := hS.mem
  have hU := hS.ua
  obtain ⟨hJ, hUJ⟩ := MemU.ofJoin hE hM hU hfJ h1 h2 h3 h4 hgrd
  have hLs := lsep_of hE hS.ext2
  have hLL : ∀ a n, InRanges a n L → InRanges a n Lk := fun a n h => hS.ext2.inRanges_old (hE.ext.inRanges_old h)
  have htw := hl.tw; have hvw := hl.vw; have hiw := hl.iw; have hti := hl.ti
  obtain ⟨hJ2, hUJ2⟩ := MemU.call hE hJ hUJ (cs := [((s.regs 4).toNat - 248, (s.regs 4).toNat - 240)])
    (ext := [(t, t + 8 * vl)])
    (hq3.mono fun a n ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      refine ⟨ho.2, ?_⟩; omega)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only; omega)
    (fun a n h => by
      simp only [wsL, List.cons_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
    ⟨fun a n hin ho => hq3.readLE a n (by
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)⟩ hLL hinv1
  have hV1 : natVal M1 vp vl = natVal s.mem vp vl := by
    unfold natVal
    rw [hfJ.readLE _ _ (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega)]
    exact hM.vs _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hvn : s.mem.readLE (vp + 8 * (vl - 1)) 8 ≠ 0 := by
    rcases hE.pre.vn with h | h
    · omega
    · exact h
  rw [hV1] at hq1
  obtain ⟨hT, htop⟩ := sh_val s.mem w vp t vl sh hv2 hvn hsh hq1
  refine ⟨hJ2, hUJ2, hT, htop, fun a n i1 i2 => ?_⟩
  rw [hq3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
    hfJ.readLE _ _ (by simp only [scrJ, outside_cons, outside_nil, and_true]; omega)]
  exact hS.is a n i1 i2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
theorem shA (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C S)
    (hgrd : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (sh : Nat) (hsh : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh) (hsh0 : sh ≠ 0)
    (Q : State → Prop)
    (k : ∀ T, AtS1 R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hil9 := hl.il9; have hvil := hl.vil
  have ht48 := hl.t48; have hv48 := hl.v48
  have hM := hS.mem
  have m1 := hM.vlS; have m2 := hM.vpS
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx := hS.x15; have hdf := hS.df
  have hr0 := hS.r0; have hr3 := hS.r3; have hr1 := hS.r1; have hr6 := hS.r6; have hr7 := hS.r7; have hr8 := hS.r8
  have hvt := Janus.Arm64.Memory.readLE_lt s.mem (vp + 8 * (vl - 1)) 8
  have hvn : s.mem.readLE (vp + 8 * (vl - 1)) 8 ≠ 0 := by
    rcases hE.pre.vn with h | h
    · omega
    · exact h
  have hshb := (AsmDiv.clz_norm64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) hvn hvt).1
  rw [hsh] at hshb
  have hr2 : S.regs 2 = BitVec.ofNat 64 (63 - sh) := by rw [hS.r2, hsh]
  have hU := hS.ua
  have hc40 := hU.c40; have hcap := hU.cap
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hE.pre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg hal
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hSacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hSacc]; exact hg2
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
  -- `DX = -((63 - sh) - 63) = sh`
  have hdx := dx_sh sh (Nat.pos_of_ne_zero hsh0) hshb
  have hne : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  -- `lshVU`'s precondition facts (callee `RSP = RSP - 312`)
  have hLs := lsep_of hE hS.ext2
  have hzH : Held R Lk t (8 * vl) := hS.ext2.held hl.theld
  have hzacc : S.mem.accessible t (8 * vl) true = true := by rw [hSacc]; exact hE.scr.acc
  have hxacc : S.mem.accessible vp (8 * vl) false = true := by rw [hSacc]; exact hE.pre.vo.2.1
  have htw' := hl.tw; have hvw' := hl.vw; have htv := hl.tv
  have hro : Outside ((s.regs 4).toNat - 312 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hga := hE.pre.ce.2.2.2.2.2.1
  unfold Apart at hga
  have hgt := (wsL_parts (g_wsL hE)).1
  have htt := (wsL_parts (tls_wsL hE)).1
  have hzg : Apart t (8 * vl) ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hzt : Apart t (8 * vl) (s.fsBase.toNat - 8) 8 := by unfold Apart; omega
  have hrg : Apart ((s.regs 4).toNat - 312 + 64) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart; omega
  have hrt : Apart ((s.regs 4).toNat - 312 + 64) 8 (s.fsBase.toNat - 8) 8 := by
    have h := htw; unfold Apart at h ⊢; omega
  have hzr : Apart t (8 * vl) ((s.regs 4).toNat - 312) 72 := by unfold Apart; omega
  have hxr : Apart vp (8 * vl) ((s.regs 4).toNat - 312 + 64) 8 := by unfold Apart; omega
  have halx : vp ≤ t ∨ Apart t (8 * vl) vp (8 * vl) := Or.inr (by unfold Apart; omega)
  have hra : (6220956 : Nat) < 2 ^ 47 := by decide
  have hinv := hM.inv
  have hfsN : S.fsBase.toNat = s.fsBase.toNat := by rw [hfs]
  have hrt' : (s.regs 4).toNat - 312 + 64 + 8 ≤ S.fsBase.toNat - 8 ∨ S.fsBase.toNat - 8 ≤ (s.regs 4).toNat - 312 + 56 := by
    rw [hfsN]; have h := hrt; unfold Apart at h; omega
  have hshv : 18446744073709551616 - (18446744073709551553 + (63 - sh)) = sh := by omega
  janus64_run [m1, m2, hr2, hdx, hne, hgrd, htS, hshv, ite_self] until [shRet1] calls [lshvu impl hap R bk Lk]
  rename_i w _ _ hq hinv1 hgd _
  have e312 : (s.regs 4 - 312#64).toNat = (s.regs 4).toNat - 312 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  obtain ⟨q1, q2, q3⟩ := lshQ (z := t) (n := vl) (x := vp) (r := sh)
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312]; simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)) hq
  simp only [Janus.Amd64.Tactic.setRegF_apply, ↓reduceIte, e312] at q1 q2 q3
  obtain ⟨hJ2, hUJ2, hT, htop, his⟩ := sh1_post hE hS hgrd hsh
    (by simp only [scrJ]; janus_frame)
    (by simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    (by simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by have := hU.p48; simp only [Nat.reducePow]; omega))
    (by simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega))
    q1 q3 hinv1
  refine k _ ⟨?pc, ?sp, ?r5, ?fs, ?df, hJ2, hUJ2, hS.ext2, hS.bud2, Nat.pos_of_ne_zero hsh0, hshb, hT, htop, his, ?reg⟩
  all_goals (try janus64_simp)
  case fs => exact hfs
  case reg =>
    rw [hrg1]; (try simp only [Janus.Arm64.Memory.regions_writeLE]); exact hS.reg

end FvModexp.Amd64.Q.DivLarge
