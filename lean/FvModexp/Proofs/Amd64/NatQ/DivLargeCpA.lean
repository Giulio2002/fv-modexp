import FvModexp.Proofs.Amd64.NatQ.DivLargeCpRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeCpA.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `shift = 0` (natdiv.go:609-610), from `joinU` through `copy(v, vIn)`'s `memmove`

`+0x216`: store `SI = C` (`RSP - 184`), `DI = il + 1` (`- 200`), `R8 = P` (`- 104`); `DX = 63 - bsr vIn[n-1]`
(`= clz = 0` here) → `- 176`; `TESTQ DX; JNE` not taken; `BX = min(len v, len vIn) = n` (`R11 = len vIn` from
`RSP + 40`); `CMPQ AX = t, R13 = vIn.ptr` (`RSP + 32`); `JE` not taken (`t` is the scratch, apart from `vIn`);
`memmove(t, vIn, 8n)` (`CALL` at `+0x272`); stop at the return `+0x277` (`AtV`). Port of `Arm64/Nat/DivLargeCpA.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
theorem cpA (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C S)
    (hgrd : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (hclz : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0) (Q : State → Prop)
    (k : ∀ T, AtV R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C T →
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
  have hr2 : S.regs 2 = 63#64 := by rw [hS.r2, hclz]
  have hU := hS.ua
  have hc40 := hU.c40; have hcap := hU.cap
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  obtain ⟨⟨htb, htr, htg⟩, htrt, htw⟩ := hE.pre.ce.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hE.pre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg hal
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hSacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hSacc]; exact hg2
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := hM.tls
  have htv : (BitVec.ofNat 64 t = BitVec.ofNat 64 vp) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; have := hl.tv; omega
  have hne1 : ((18446744073709551616 - vp + t) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; have := hl.tv; omega
  have hne2 : ((18446744073709551616 - t + vp) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; have := hl.tv; omega
  have hsh : BitVec.ofNat 64 vl <<< 3 = BitVec.ofNat 64 (8 * vl) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft]; simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hok : R.ok (cA "runtime.memmove") [t, vp, 8 * vl] := hE.pre.sv.2.1 _ _ _ (by omega)
  have hLs := lsep_of hE hS.ext2
  have hvh : Held R Lk t (8 * vl) := hS.ext2.held hl.theld
  have hdacc : S.mem.accessible t (8 * vl) true = true := by rw [hSacc]; exact hE.scr.acc
  have hsacc : S.mem.accessible vp (8 * vl) false = true := by rw [hSacc]; exact hE.pre.vo.2.1
  have htw' := hl.tw; have hvw' := hl.vw
  have hinv := hM.inv
  have hvh' : InRanges t (8 * vl) Lk ∨ Outside t (8 * vl) R.rt := hvh
  have hga := hE.pre.ce.2.2.2.2.2.1
  unfold Apart at hga
  janus64_run [m1, m2, hr2, htv, hne1, hne2, hsh, hgrd, htS, ite_self] until [cpRet1] calls [hmv Lk bk]
  rename_i m _ _ hF2 hLF2 hinv2 hcp
  -- the memory at the call: the four `joinU` slot stores and the pushed return address
  generalize hG : (((((S.mem.writeLE ((s.regs 4).toNat - 184) 8 C).writeLE ((s.regs 4).toNat - 200) 8 (il + 1)).writeLE
        ((s.regs 4).toNat - 104) 8 P).writeLE ((s.regs 4).toNat - 176) 8 0).writeLE
        ((s.regs 4).toNat - 312) 8 6220695) = M1 at hF2 hLF2 hcp
  have hW : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      M1.readLE a n = S.mem.readLE a n := by
    intro a n h
    rw [← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hLL : ∀ a n, InRanges a n L → InRanges a n Lk := fun a n h => hS.ext2.inRanges_old (hE.ext.inRanges_old h)
  obtain ⟨hJ, hUJ⟩ := MemU.ofJoin hE hM hU (M' := M1) (sh := 0) (by rw [← hG]; simp only [scrJ]; janus_frame)
    (by
      rw [← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)])
    (by
      rw [← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)])
    (by
      have := hU.p48
      rw [← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)])
    (by
      rw [← hG, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self])
    hgrd
  obtain ⟨hJ2, hUJ2⟩ := MemU.call hE hJ hUJ hF2
    (fun r hr => by
      simp only [calleeStack64, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
    (fun a n h => by
      simp only [wsL, List.cons_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
    hLF2 hLL hinv2
  have hvS : ∀ a n, vp ≤ a → a + n ≤ vp + 8 * vl → S.mem.readLE a n = s.mem.readLE a n := hM.vs
  have hcp2 : ∀ (o n : Nat), o + n ≤ 8 * vl → m.readLE (t + o) n = s.mem.readLE (vp + o) n := by
    intro o n hon
    have hsub : Janus.Contracts.Mem.Copied M1 m (t + o) (vp + o) n := fun i hi => by
      have := hcp (o + i) (by omega)
      rw [show t + (o + i) = t + o + i by omega, show vp + (o + i) = vp + o + i by omega] at this
      exact this
    rw [FvModexp.Expmc.readLE_of_copied hsub, hW _ _ (by omega), hvS _ _ (by omega) (by omega)]
  refine k _ ⟨?pc, ?sp, ?r5, ?r14, ?fs, ?x15, ?df, hJ2, hUJ2, hS.ext2, hS.bud2, ?vval, ?vtop, ?is, ?reg⟩
  case vval => show natVal m t vl = _; have := hcp2 0 (8 * vl) (by omega); simpa only [natVal, Nat.add_zero] using this
  case vtop => show m.readLE _ 8 = _; exact hcp2 (8 * (vl - 1)) 8 (by omega)
  case is =>
    intro a n h1 h2
    show m.readLE a n = _
    have hiw := hl.iw; have hti := hl.ti
    have hm : m.readLE a n = M1.readLE a n := by
      rcases (hE.pre.io.2.2.2.1.sub h1 h2) with hi | ho
      · exact hLF2.readLE a n (hS.ext2.inRanges_old (hE.ext.inRanges_old hi))
          (by simp only [outside_cons, outside_nil, and_true]; omega)
      · exact hF2.readLE a n (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨ho, by omega, by omega⟩, by omega⟩)
    rw [hm, hW _ _ (by omega)]; exact hS.is a n h1 h2
  all_goals (try janus64_simp)
  case reg =>
    rename_i hrg1
    rw [hrg1]; (try simp only [Janus.Arm64.Memory.regions_writeLE]); exact hS.reg
  case pc => rw [← hG, Janus.Arm64.Memory.readLE_writeLE_self]; rfl
  all_goals (first | exact hx | exact hfs | exact hdf | exact h14 | skip)

end FvModexp.Amd64.Q.DivLarge
