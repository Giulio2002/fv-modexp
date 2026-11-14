import FvModexp.Proofs.Amd64.Exp.P2DZero
import FvModexp.Proofs.Amd64.Exp.P2DMk
import FvModexp.Proofs.Common.ExpPow2
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `logM = 1` (agent asm s67; amd64 twin of infra's arm64 `P2DOne`)

`oneP`: from `oneE` (memory `W0`): `x[0]` even → `z[:0]` (`oneR0`); odd and `cap z ≠ 0` → `z[0] := 1`, `z[:1]`
(`oneR1`); odd and `cap z = 0` → `makeslice(Word, 1, 1)` (`oneRM` → `mkCallD` → `mkR`), the fresh one-word result
(`post_rt`). Value `X^Y mod 2 = x[0] mod 2` (`val_mod2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

/-- `x^y mod 2` is the parity of the low word -/
theorem val_mod2 (m : Memory) (xp xl Y : Nat) (hxl : 0 < xl) (hY : 0 < Y) :
    natVal m xp xl ^ Y % 2 = m.readLE xp 8 % 2 := by
  rw [Exp.pow_mod_one_odd _ _ hY]
  have := Expmc.readLE_wd m xp 0 xl hxl
  simp only [Nat.mul_zero, Nat.add_zero, Exp.wd, Nat.pow_zero, Nat.div_one] at this
  rw [this, natVal, Nat.mod_mod_of_dvd _ (by rw [Exp.B_def]; decide)]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

/-- `PostD` from the epilogue facts and the `CPostR` body -/
theorem postD_of (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) {v sp : Nat}
    (hsp : sp + 0x70 = (s.regs 4).toNat) {S s' : State} (hE : Epi S s' sp (s.regs 5).toNat)
    (e14 : S.regs 14 = s.regs 14) (efs : S.fsBase = s.fsBase) (ex : S.xmm 15 = s.xmm 15) (edf : S.df = s.df)
    (hc : s'.fsBase = s.fsBase → s'.df = s.df → NHyp.CPostR R b L stk A zp zc st v cst s s') :
    PostD R b L stk A cst zp zc st v s s' := by
  obtain ⟨h4, h5, h14, hfs, hx, hdf⟩ := hE
  obtain ⟨⟨⟨-, ⟨hbel, h48, -⟩, -⟩, -⟩, -⟩ := hP
  try simp only [regSP] at hbel h48
  have h5' : BitVec.ofNat 64 (s.regs 5).toNat = s.regs 5 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (BitVec.isLt _))
  refine ⟨⟨?_, h5.trans h5', h14.trans e14, hx.trans ex⟩, hc (hfs.trans efs) (hdf.trans edf)⟩
  rw [h4]; bv_omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `logM = 1`, `x[0]` odd, `cap z = 0`: `makeslice(Word, 1, 1)`, `[p] := 1`, result `(p, 1, 1)` -/
theorem oneMk {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : PreD R b L stk A cst zp zl 0 st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hcst : allocCost 8 ≤ cst) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) {SP : Nat}
    (hSP0 : (s.regs 4).toNat = SP)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 oneE) (esp : S.regs 4 = BitVec.ofNat 64 (SP - 0x70))
    (e1 : S.regs 1 = BitVec.ofNat 64 0) (e6 : S.regs 6 = BitVec.ofNat 64 xp) (e8 : S.regs 8 = BitVec.ofNat 64 xl)
    (e14' : S.regs 14 = s.regs 14) (efs : S.fsBase = s.fsBase) (ex : S.xmm 15 = s.xmm 15) (edf : S.df = s.df)
    (hm : S.mem = W0 s.mem (SP - 0x70) (s.regs 5).toNat zp xp)
    (hxl0 : 0 < xl) (hxl64 : xl < 2 ^ 64) (hxa8 : S.mem.accessible xp 8 false = true) (hxp : xp + 8 ≤ 2 ^ 48)
    (hx1 : S.mem.readLE xp 8 % 2 = 1) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S (PostD R b L stk A cst zp 0 st 1 s) := by
  subst hSP0
  have hP0 := hP
  obtain ⟨q1, q2, q3, q4, q5⟩ := epi_of hP hk hA hra
  obtain ⟨hC, -⟩ := hP
  obtain ⟨⟨-, ⟨hle, h48, hacc⟩, -, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hcb, -⟩ := id hC
  simp only [regSP] at hle h48 hacc
  rw [← hm] at q2 q3 q4
  have hsp0 : 0x70 ≤ (s.regs 4).toNat := by omega
  have hF0 : MemFrame s.mem S.mem (ownW s stk A) := by rw [hm]; exact w0_own (by omega) hA hsp0
  generalize hSP : (s.regs 4).toNat = SP at *
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hacc8 : S.mem.accessible (SP - 0x70 - 8) 8 true = true := by
    rw [hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  refine oneRM hpc esp (by omega) q1 hacc8 (by rw [e1]) e6 e8 hxl0 hxl64 hxa8 hxp
    hx1 fun T t0 t4 t0' t3 t1 t5 t14 tfs tx tdf tm => ?_
  have t4N : (T.regs 4).toNat + 0x78 = SP := by rw [t4, BitVec.toNat_ofNat]; omega
  have hFT : MemFrame s.mem T.mem (ownW s stk A) := by
    rw [tm]
    refine (MemFrame.writeLE (hF0.mono fun a k ho => by rw [outside_append] at ho; exact ho.1) _
      (r := (SP - 0x70 - 8, SP - 0x70)) (List.mem_append_right _ (List.mem_singleton_self _)) (by simp only; omega) (by simp only; omega)).mono fun a k ho => ?_
    rw [outside_append]; refine ⟨ho, ?_⟩
    simp only [ownW, hSP, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hrgT : T.mem.regions = s.mem.regions := by
    rw [tm, hm]; simp only [W0, Janus.Arm64.Memory.regions_writeLE]
  have hraT : T.mem.readLE (T.regs 4).toNat 8 = mkRa := by
    rw [tm, show (T.regs 4).toNat = SP - 0x70 - 8 by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by decide)
  refine mkCallD hmk hC hk (by omega) (Nat.le_trans (blockSize_le_allocCost _ _) (Nat.le_trans hcst hcb)) T t0
    (by rw [t4N, hSP]) (t14.trans e14') hFT hrgT (by rw [hraT]; decide) t0' t3 t1
    fun ptr junk f x yh m zh kr hM => ?_
  -- back at `mkRa`
  have hcs : ∀ {a k : Nat}, (SP - 8 ≤ a ∧ a + k ≤ SP + 8) → Outside a k (R.rt ++ calleeStack64 T 4096 3) := by
    intro a k ha
    rw [outside_append]
    refine ⟨hwin.of_sub (by omega) (by omega), ?_⟩
    simp only [calleeStack64, outside_cons, outside_nil, and_true]; omega
  have hTr : ∀ {a k : Nat}, (SP - 8 ≤ a ∧ a + k ≤ SP + 8) → T.mem.readLE a k = S.mem.readLE a k := by
    intro a k ha; rw [tm]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hsz := hM.sz
  have hb48 := hM.b48
  have k0 : (retState64 T junk [ptr] f x yh m zh kr).regs 0 = BitVec.ofNat 64 ptr.toNat := by
    simp [retState64, callRegs64_apply]
  have hpw : Apart ptr.toNat (blockSize 8 true) (SP - stk) (stk + A) := (hM.rin.apart hwin).symm
  unfold Apart at hpw
  refine mkR (S := retState64 T junk [ptr] f x yh m zh kr) (sp := SP - 0x70) (bp := (s.regs 5).toNat)
    (p := ptr.toNat) ?_ ?_ q1 ?_ ?_ ?_ q5 ?_ ?_ (by omega) (by omega) fun s' hE a0 a3 a1 am => ?_
  · simp only [retState64, retAddrOf, hraT]
  · simp only [retState64, callRegs64_apply, if_pos, t4]; bv_omega
  · simp only [retState64]; rw [hM.mf.accessible, tm, Janus.Arm64.Memory.accessible_writeLE]
    exact q2
  · simp only [retState64]
    rw [hM.mf.readLE _ _ (hcs ⟨by omega, by omega⟩), hTr ⟨by omega, by omega⟩]; exact q3
  · simp only [retState64]
    rw [hM.mf.readLE _ _ (hcs ⟨by omega, by omega⟩), hTr ⟨by omega, by omega⟩]; exact q4
  · simp only [retState64, callRegs64_apply]; simp
  · simp only [retState64]; exact Janus.Arm64.Memory.accessible_mono _ hM.acc (Nat.le_refl _) (by omega)
  -- the fresh one-word result
  have k14 : (retState64 T junk [ptr] f x yh m zh kr).regs 14 = s.regs 14 := by
    simp only [retState64, callRegs64_apply]; simp [t14, e14']
  refine postD_of hP0 (by omega) hE k14 (by simp only [retState64]; rw [tfs, efs]) (by simp only [retState64]; simp [tx, ex])
    (by simp only [retState64]; rw [tdf, edf]) fun hfs hdf => ?_
  simp only [retState64] at am
  have hin8 : InRanges ptr.toNat 8 R.rt := hM.rin.sub (Nat.le_refl _) (by omega)
  have hap8 : ApartAll ptr.toNat 8 L := ApartAll.sub' hM.rap (Nat.le_refl _) (by omega)
  have hL' : InRanges ptr.toNat 8 (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) :=
    ⟨(ptr.toNat, ptr.toNat + blockSize 8 true), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _,
      by simp only; omega⟩
  have hW : MemFrame m (m.writeLE ptr.toNat 8 1) [(ptr.toNat, ptr.toNat + 8)] :=
    (MemFrame.refl _ _).writeLE_inRanges _ ⟨(ptr.toNat, ptr.toNat + 8), by simp, by simp only; omega, by simp only; omega⟩
  have hFm : MemFrame s.mem (m.writeLE ptr.toNat 8 1) (R.rt ++ ownW s stk A) := by
    refine MemFrame.trans hFT (MemFrame.trans hM.mf hW (fun a k ho => ⟨ho, ?_⟩)) (fun a k ho => ⟨?_, ?_⟩)
    · rw [outside_append] at ho
      have := hin8.apart ho.1
      unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [outside_append] at ho; exact ho.2
    · rw [outside_append] at ho ⊢
      refine ⟨ho.1, ?_⟩
      have := ho.2
      simp only [calleeStack64, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢
      omega
  have hLFm : LiveFrame s.mem (m.writeLE ptr.toNat 8 1) L [] :=
    ((LiveFrame.of_win hFT hLs').trans hM.lf fun _ _ h => h).writeLE 1 hap8.outside
  have hx : LiveExt R L (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) :=
    LiveExt.single (by rw [show ptr.toNat + blockSize 8 true - ptr.toNat = blockSize 8 true by omega]; exact hM.rin)
      (by rw [show ptr.toNat + blockSize 8 true - ptr.toNat = blockSize 8 true by omega]; exact hM.rap)
  have hinv' : R.inv (b - blockSize 8 true) (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) (s.regs 14).toNat
      (view R.rt (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) (m.writeLE ptr.toNat 8 1)) := by
    have := hM.inv
    rw [t14, e14'] at this
    refine Expmc.inv_frame hW (fun r hr => ?_) this
    simp only [List.mem_singleton] at hr; subst hr; simp only
    rw [show ptr.toNat + 8 - ptr.toNat = 8 by omega]; exact Or.inl hL'
  refine post_rt hC hFm hLFm hx (by have := hM.rc; omega) hinv' ⟨?_, Or.inr ?_, Nat.le_refl _, by decide,
    fun _ => ⟨hM.al, Or.inl hL', ?_, by have := hM.b48; omega⟩, Or.inr ⟨Nat.le_refl _, hin8, hap8⟩⟩ am hfs hdf
    (a0.trans k0) a3 a1
  · show (m.writeLE ptr.toNat 8 1).readLE ptr.toNat (8 * 1) = 1
    rw [Janus.Arm64.Memory.readLE_writeLE_self]
  · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self]; decide
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hM.acc (Nat.le_refl _) (by omega)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`logM = 1`** (see the module doc) -/
theorem oneP {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hcst : allocCost 8 ≤ cst) (hlm : lm = 1) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 oneE)
    (hR : RE s S ((s.regs 4).toNat - 0x70) (s.regs 14).toNat zp zl zc st xp xl xc yp yl lm)
    (hm : S.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  have hP0 := hP
  obtain ⟨q1, q2, q3, q4, q5⟩ := epi_of hP hk hA hra
  obtain ⟨hC, hX, hY, -, -, -, -⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hle, h48, hacc⟩, -, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, ⟨hz40, hzL, hzW⟩, hins, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hcb, -⟩ := hC'
  obtain ⟨⟨-, hxa, hx48, -, hxw⟩, -⟩ := hins xp xl (by simp)
  obtain ⟨esp, e5, e0, e3, e1, -, e6, e8, -, -, -, -, e14, efs, ex, edf⟩ := hR
  simp only [regSP] at hle h48 hacc
  subst hlm
  rw [← hm] at q2 q3 q4
  have hsp0 : 0x70 ≤ (s.regs 4).toNat := by omega
  have hF0 : MemFrame s.mem S.mem (ownW s stk A) := by rw [hm]; exact w0_own (by omega) hA hsp0
  have e14' : S.regs 14 = s.regs 14 := by
    rw [e14]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (BitVec.isLt _))
  generalize hSP : (s.regs 4).toNat = SP at *
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  simp only [win, hSP, outside_cons, outside_nil, and_true] at hxw
  have rx : S.mem.readLE xp 8 = s.mem.readLE xp 8 := by
    rw [hm]; exact w0_rd (by omega)
  have hxa8 : S.mem.accessible xp 8 false = true := by
    rw [hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hxa (Nat.le_refl _) (by omega)
  have hv := val_mod2 s.mem xp xl (natVal s.mem yp yl) hxl0 hY
  rw [Nat.pow_one, hv]
  by_cases hx0 : s.mem.readLE xp 8 % 2 = 0
  · rw [hx0]
    refine oneR0 hpc esp q1 q2 q3 q4 q5 e6 e8 hxl0 (by omega) hxa8 (by omega) (by rw [rx]; exact hx0)
      fun s' hE a0 a3 a1 am => postD_of hP0 (by omega) hE e14' efs ex edf fun hfs hdf => ?_
    exact post_own hC (by omega) (zs := []) (by rw [List.append_nil, am]; exact hF0) (fun r hr => by simp at hr)
      (Nat.zero_le _) (by simp [natVal]) (Or.inl rfl) rfl hfs hdf (a0.trans e0) (by rw [a3]) (a1.trans e1)
  have hx1 : s.mem.readLE xp 8 % 2 = 1 := by omega
  rw [hx1]
  by_cases hzc : 0 < zc
  · obtain ⟨z8, -, zacc, z48⟩ := hzL hzc
    have hzo := (hzW hzc).1
    simp only [win, hSP, outside_cons, outside_nil, and_true] at hzo
    refine oneR1 hpc esp q1 q2 q3 q4 q5 e0 e1 hzc (by omega)
      (by rw [hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
          exact Janus.Arm64.Memory.accessible_mono _ zacc (Nat.le_refl _) (by omega))
      (by omega) e6 e8 hxl0 (by omega) hxa8 (by omega) (by rw [rx]; exact hx1) (by omega)
      fun s' hE a0 a3 a1 am => postD_of hP0 (by omega) hE e14' efs ex edf fun hfs hdf => ?_
    refine post_own hC (by omega) (zs := [(zp, zp + 8 * zc)])
      (MemFrame.writeLE (hF0.mono fun a k ho => by rw [outside_append] at ho; exact ho.1) 1 (r := (zp, zp + 8 * zc)) (by simp) (by simp only; omega) (by simp only; omega))
      (fun r hr => by simp at hr; exact ⟨hr, hzc⟩) (by omega) ?_ (Or.inr ?_) am hfs hdf (a0.trans e0) a3
      (a1.trans e1)
    · show (Janus.Arm64.Memory.writeLE _ zp 8 1).readLE zp (8 * 1) = 1
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
    · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self]; decide
  have hzc0 : zc = 0 := by omega
  subst hzc0
  exact oneMk hmk hP0 hk hA hcst (by rw [hSP]; exact hra) hSP S hpc esp e1 e6 e8 e14' efs ex edf hm hxl0 (by omega) hxa8 (by omega)
    (by rw [rx]; exact hx1)

end

end FvModexp.Amd64.P2D
