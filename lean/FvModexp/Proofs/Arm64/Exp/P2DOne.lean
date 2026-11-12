import FvModexp.Proofs.Arm64.Exp.P2DEnt
import FvModexp.Proofs.Arm64.Exp.P2DPost
import FvModexp.Proofs.Arm64.Exp.P2DMk
import FvModexp.Proofs.Common.ExpPow2
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `logM = 1` — `return z.setWord(x[0] & 1)` (agent infra)

`oneP`: from `oneE` (after `ent`) to the return, the three shapes (`z[:0]`; `z[0] = 1` in place; a fresh
`makeslice(Word, 1, 1)`), post `PostD` with value `X^Y mod 2 = x[0] mod 2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`logM = 1`** (see the module doc) -/
theorem oneP {impl : List Segment} (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hcst : allocCost 8 ≤ cst) (hlm : lm = 1) (hzp : zp < 2 ^ 64) (hxp : xp < 2 ^ 64)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 oneE)
    (hR : RE S (s.sp.toNat - 112) (s.regs 28).toNat zp zl zc st xp xl xc yp yl yc lm (s.regs 18))
    (hm : S.mem = W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S
      (PostD R b L stk A cst zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s) := by
  obtain ⟨hC, hX, hY, -, -, -, -⟩ := hP
  have hC' := hC
  obtain ⟨⟨-, ⟨hal, hle, h48, hacc⟩, -, hwrt, -, -, hLs, -⟩, -, -, -, -, -, ⟨hz40, hzL, hzW⟩, hins, -, -, -, -, -, -,
    -, -, -, -, -, -, hcb, -⟩ := hC'
  obtain ⟨⟨-, hxa, hx48, -, hxw⟩, -⟩ := hins xp xl (by simp)
  obtain ⟨esp, e0, -, e2, -, e4, e5, -, -, -, -, -, e18, e28, e29⟩ := hR
  subst hlm
  generalize hSP : s.sp.toNat = SP at *
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hsp1 : 8 ≤ SP - 112 := by omega
  have hr64 : (s.regs 30).toNat < 2 ^ 64 := BitVec.isLt _
  have h29 : (s.regs 29).toNat < 2 ^ 64 := BitVec.isLt _
  have hepi : Epi (W0 s.mem (SP - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) (SP - 112)
      (s.regs 29).toNat (s.regs 30).toNat := by
    refine ⟨by omega, hsp1, by omega, ?_, w0_fp hsp1 h29, w0_lr hsp1 hr64, hr4, hr48⟩
    simp only [W0, Memory.accessible_writeLE]
    exact Memory.accessible_weaken _ (Memory.accessible_mono _ hacc (by omega) (by omega))
  have hxw' : Outside xp 8 [(SP - 112 - 8, SP - 112 + 184)] := by
    simp only [win, hSP, outside_cons, outside_nil, and_true] at hxw ⊢; omega
  have rx := w0_rd (r29 := (s.regs 29).toNat) (r30 := (s.regs 30).toNat) (zp := zp) (xp := xp) (yp := yp) (M := s.mem) hsp1 hxw'
  have hxa8 : (W0 s.mem (SP - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp).accessible xp 8 false = true := by
    simp only [W0, Memory.accessible_writeLE]; exact Memory.accessible_mono _ hxa (Nat.le_refl _) (by omega)
  have hv := val_mod2 s.mem xp xl (natVal s.mem yp yl) hxl0 hY
  rw [Nat.pow_one, hv]
  have hF0 := w0_frame s.mem (r29 := (s.regs 29).toNat) (r30 := (s.regs 30).toNat) (zp := zp) (xp := xp) (yp := yp)
    hsp1
  have hF0' : MemFrame s.mem (W0 s.mem (SP - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp) (ownW s stk A) :=
    hF0.mono fun a k ho => by simp only [ownW, hSP, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hfin : ∀ s' : State, s'.sp = BitVec.ofNat 64 (SP - 112 + 112) → s'.regs 18 = S.regs 18 →
      s'.regs 28 = S.regs 28 → s'.regs 29 = BitVec.ofNat 64 (s.regs 29).toNat →
      s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 := by
    intro s' a1 a2 a3 a4
    refine ⟨by rw [a1]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hSP]; omega, a2.trans e18,
      a3.trans (e28.trans (by simp)), a4.trans (by simp)⟩
  rw [show s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat by simp]
  by_cases hx0 : s.mem.readLE xp 8 % 2 = 0
  · rw [hx0]
    refine oneR0 impl _ (SP - 112) xp xl _ _ _ hepi hxl0 (by omega) hxa8 hxp (by rw [rx]; exact hx0) S hpc esp e4 e5 hm
      fun s' a1 a2 a3 a4 a5 a6 a7 a8 => ⟨(hfin s' a1 a5 a6 a7).1, (hfin s' a1 a5 a6 a7).2.1, (hfin s' a1 a5 a6 a7).2.2.1,
        (hfin s' a1 a5 a6 a7).2.2.2, ?_⟩
    refine post_own hC (by omega) (zs := []) (by simpa only [List.append_nil] using hF0') (fun r hr => by simp at hr)
      (Nat.zero_le _) (by simp [natVal]) (Or.inl rfl) a8 (a2.trans e0) a3 (a4.trans e2)
  have hx1 : s.mem.readLE xp 8 % 2 = 1 := by omega
  rw [hx1]
  by_cases hzc : 0 < zc
  · obtain ⟨z8, -, zacc, z48⟩ := hzL hzc
    have hzo := (hzW hzc).1
    simp only [win, hSP, outside_cons, outside_nil, and_true] at hzo
    refine oneR1 impl _ (SP - 112) zp zc xp xl _ _ _ hepi hxl0 (by omega) hxa8 hxp (by rw [rx]; exact hx1) hzc
      (by omega) hzp (by simp only [W0, Memory.accessible_writeLE]; exact Memory.accessible_mono _ zacc (Nat.le_refl _) (by omega))
      (by omega) S hpc esp e0 e2 e4 e5 hm
      fun s' a1 a2 a3 a4 a5 a6 a7 a8 => ⟨(hfin s' a1 a5 a6 a7).1, (hfin s' a1 a5 a6 a7).2.1, (hfin s' a1 a5 a6 a7).2.2.1,
        (hfin s' a1 a5 a6 a7).2.2.2, ?_⟩
    refine post_own hC (by omega) (zs := [(zp, zp + 8 * zc)])
      (MemFrame.writeLE (hF0'.mono fun a k ho => by rw [outside_append] at ho; exact ho.1) 1 (r := (zp, zp + 8 * zc))
        (by simp) (by simp only; omega) (by simp only; omega)) (fun r hr => by simp at hr; exact ⟨hr, hzc⟩)
      (by omega) ?_ (Or.inr ?_) a8 a2 a3 a4
    · show (Memory.writeLE _ zp 8 1).readLE zp (8 * 1) = 1
      rw [Memory.readLE_writeLE_self]
    · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Memory.readLE_writeLE_self]; decide
  have hzc0 : zc = 0 := by omega
  subst hzc0
  have hrgW : (W0 s.mem (SP - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp).regions = s.mem.regions := by
    simp only [W0, Memory.regions_writeLE]
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  refine oneRM impl _ _ (SP - 112) xp xl _ hxl0 (by omega) hxa8 hxp (by rw [rx]; exact hx1) S hpc esp e2 e4 e5 hm
    fun T t0 tsp t0' t1 t2 t30 t18 t28 t29 tm => ?_
  have tspN : T.sp.toNat + 112 = SP := by rw [tsp, esp, BitVec.toNat_ofNat]; omega
  refine mkCallD hmk _ _ hC (by omega) (by omega) (Nat.le_trans hcst hcb) T t0 (by rw [tspN]; exact hSP.symm)
    (t28.trans (e28.trans (by simp))) (by rw [tm]; exact hF0') (by rw [tm]; exact hrgW) t0' t1 t2 t30
    fun ptr junk f v m ex ep hM hrg2 => ?_
  have hcs : ∀ {a k : Nat}, (SP - 112 - 8 ≤ a ∧ a + k ≤ SP - 112 + 8) → Outside a k (R.rt ++ calleeStack T 4096 3) := by
    intro a k ha
    rw [outside_append]
    refine ⟨hwin.of_sub (by omega) (by omega), ?_⟩
    simp only [calleeStack, outside_cons, outside_nil, and_true]; omega
  have hepi' : Epi m (SP - 112) (s.regs 29).toNat (s.regs 30).toNat := by
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hepi
    rw [← tm] at q4 q5 q6
    refine ⟨q1, q2, q3, by rw [hM.mf.accessible]; exact q4, by rw [hM.mf.readLE _ _ (hcs ⟨by omega, by omega⟩)]; exact q5,
      by rw [hM.mf.readLE _ _ (hcs ⟨by omega, by omega⟩)]; exact q6, q7, q8⟩
  have hsz := hM.sz
  have hpw : Apart ptr.toNat (blockSize 8 true) (SP - stk) (stk + A) := (hM.rin.apart hwin).symm
  unfold Apart at hpw
  refine mkR impl _ (SP - 112) ptr.toNat _ _ m hepi' ptr.isLt
    (Memory.accessible_mono _ hM.acc (Nat.le_refl _) (by omega)) (by omega) _ (by simp [retStateX, t30])
    (by simp only [retStateX]; rw [tsp, esp]) (by simp [retStateX, callRegs]) rfl
    fun s' a1 a2 a3 a4 a5 a6 a7 a8 => ?_
  replace a5 : s'.regs 18 = T.regs 18 := by rw [a5]; rfl
  replace a6 : s'.regs 28 = T.regs 28 := by rw [a6]; rfl
  refine ⟨(hfin s' a1 (a5.trans t18) (a6.trans t28) a7).1, (hfin s' a1 (a5.trans t18) (a6.trans t28) a7).2.1,
    (hfin s' a1 (a5.trans t18) (a6.trans t28) a7).2.2.1, (hfin s' a1 (a5.trans t18) (a6.trans t28) a7).2.2.2, ?_⟩
  -- the fresh one-word result
  have hin8 : InRanges ptr.toNat 8 R.rt := hM.rin.sub (Nat.le_refl _) (by omega)
  have hap8 : ApartAll ptr.toNat 8 L := ApartAll.sub' hM.rap (Nat.le_refl _) (by omega)
  have hL' : InRanges ptr.toNat 8 (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) :=
    ⟨(ptr.toNat, ptr.toNat + blockSize 8 true), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _,
      by simp only; omega⟩
  have hMf : MemFrame T.mem m (R.rt ++ calleeStack T 4096 3) := hM.mf
  rw [tm] at hMf
  have hW : MemFrame m (m.writeLE ptr.toNat 8 1) [(ptr.toNat, ptr.toNat + 8)] :=
    (MemFrame.refl _ _).writeLE_inRanges _ ⟨(ptr.toNat, ptr.toNat + 8), by simp, by simp only; omega, by simp only; omega⟩
  have hFm : MemFrame s.mem (m.writeLE ptr.toNat 8 1) (R.rt ++ ownW s stk A) := by
    refine MemFrame.trans hF0' (MemFrame.trans hMf hW (fun a k ho => ⟨ho, ?_⟩)) (fun a k ho => ⟨?_, ?_⟩)
    · rw [outside_append] at ho
      have := hin8.apart ho.1
      unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [outside_append] at ho; exact ho.2
    · rw [outside_append] at ho ⊢
      refine ⟨ho.1, ?_⟩
      have := ho.2
      simp only [calleeStack, tsp, esp, ownW, hSP, BitVec.toNat_ofNat, outside_cons, outside_nil, and_true] at this ⊢
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hLFm : LiveFrame s.mem (m.writeLE ptr.toNat 8 1) L [] := by
    refine ((LiveFrame.of_win hF0' hLs').trans ?_ fun _ _ h => h).writeLE 1 hap8.outside
    have := hM.lf; rw [tm] at this; exact this
  have hx : LiveExt R L (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) :=
    LiveExt.single (by rw [show ptr.toNat + blockSize 8 true - ptr.toNat = blockSize 8 true by omega]; exact hM.rin)
      (by rw [show ptr.toNat + blockSize 8 true - ptr.toNat = blockSize 8 true by omega]; exact hM.rap)
  have hinv' : R.inv (b - blockSize 8 true) (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) (s.regs 28).toNat
      (view R.rt (L ++ [(ptr.toNat, ptr.toNat + blockSize 8 true)]) (m.writeLE ptr.toNat 8 1)) := by
    have := hM.inv
    rw [t28, e28, show BitVec.toNat (BitVec.ofNat 64 (BitVec.toNat (s.regs 28))) = (s.regs 28).toNat by simp] at this
    refine Expmc.inv_frame hW (fun r hr => ?_) this
    simp only [List.mem_singleton] at hr; subst hr; simp only
    rw [show ptr.toNat + 8 - ptr.toNat = 8 by omega]; exact Or.inl hL'
  refine post_rt hC hFm hLFm hx (by have := hM.rc; omega) hinv' ⟨?_, Or.inr ?_, Nat.le_refl _, by decide,
    fun _ => ⟨hM.al, Or.inl hL', ?_, by have := hM.b48; omega⟩, Or.inr ⟨Nat.le_refl _, hin8, hap8⟩⟩ a8 a2 a3 a4
  · show (m.writeLE ptr.toNat 8 1).readLE ptr.toNat (8 * 1) = 1
    rw [Memory.readLE_writeLE_self]
  · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Memory.readLE_writeLE_self]; decide
  · simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hM.acc (Nat.le_refl _) (by omega)
end

end FvModexp.Arm64.P2D
