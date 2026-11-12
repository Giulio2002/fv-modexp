import FvModexp.Proofs.Arm64.Nat.DivLargeShF

/-!
# `divLarge` (arm64): shift path after `lshVU(u[:il], uIn, shift)` (`fn + 0x268`): `u[il] = carry` (natdiv.go:615),
reloads → the alias test
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

/-- the frame slots kept by the shift path's frames -/
theorem sh_rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S) {M : Memory}
    (hF : MemFrame S.mem M [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112), (t, t + 8 * vl),
      (P, P + 8 * il)]) :
    M.readLE (s.sp.toNat - 96) 8 = t ∧ M.readLE (s.sp.toNat - 160) 8 = vl ∧ M.readLE (s.sp.toNat - 152) 8 = vl ∧
      M.readLE (s.sp.toNat - 176) 8 = C ∧ M.readLE (s.sp.toNat - 192) 8 = il + 1 ∧
      M.readLE (s.sp.toNat - 104) 8 = P ∧ M.readLE (s.sp.toNat + 96) 8 = vl ∧ M.readLE (s.sp.toNat + 72) 8 = il ∧
      M.readLE (s.sp.toNat + 64) 8 = ip ∧ M.readLE (s.sp.toNat + 80) 8 = ic ∧ M.readLE (s.sp.toNat + 88) 8 = vp ∧
      M.readLE (s.sp.toNat + 104) 8 = vc := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have htw := hl.tw
  have hU := hS.ua
  have hpw := hU.pw; have hcap := hU.cap
  have hM := hS.mem
  have rd : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat + 112 → (a + 8 ≤ s.sp.toNat - 120 ∨ s.sp.toNat - 112 ≤ a) →
      M.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 h3 =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact ⟨(rd _ (by omega) (by omega) (by omega)).trans hM.vt, (rd _ (by omega) (by omega) (by omega)).trans hM.vn1,
    (rd _ (by omega) (by omega) (by omega)).trans hM.vn2, (rd _ (by omega) (by omega) (by omega)).trans hS.sC,
    (rd _ (by omega) (by omega) (by omega)).trans hS.sL, (rd _ (by omega) (by omega) (by omega)).trans hS.sP,
    (rd _ (by omega) (by omega) (by omega)).trans hM.s12, (rd _ (by omega) (by omega) (by omega)).trans hM.s9,
    (rd _ (by omega) (by omega) (by omega)).trans hM.s8, (rd _ (by omega) (by omega) (by omega)).trans hM.s10,
    (rd _ (by omega) (by omega) (by omega)).trans hM.s11, (rd _ (by omega) (by omega) (by omega)).trans hM.s13⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem shC (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (sh : Nat) (hsh : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh)
    (A1 m3 A2 m4 : Memory)
    (hA1 : MemFrame S.mem A1 [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112)])
    (hA1sh : A1.readLE (s.sp.toNat - 120) 8 = sh)
    (hQ1f : MemFrame A1 m3 [(t, t + 8 * vl), (s.sp.toNat - 240, s.sp.toNat - 232)])
    (hQ1v : natVal m3 t vl = natVal A1 vp vl * 2 ^ sh % 2 ^ (64 * vl))
    (hA2 : MemFrame m3 A2 [(s.sp.toNat - 296, s.sp.toNat - 232)])
    (hQ2f : MemFrame A2 m4 [(P, P + 8 * il), (s.sp.toNat - 240, s.sp.toNat - 232)])
    (hQ2v : natVal m4 P il = natVal A2 ip il * 2 ^ sh % 2 ^ (64 * il))
    (hQ2c : m4.readLE (s.sp.toNat - 240) 8 = natVal A2 ip il * 2 ^ sh / 2 ^ (64 * il))
    (hinv4 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m4))
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x268)) (hsp : T.sp = s.sp - 304#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 312#64) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = m4)
    (hreg4 : m4.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hp48 := hU.p48; have hpw := hU.pw
  obtain ⟨hmU, hUA, hvv, hvt, huv⟩ := sh_fin hE hS hsh hA1 hA1sh hQ1f hQ1v hA2 hQ2f hQ2v hQ2c hinv4
  have hF : MemFrame S.mem m4 [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112), (t, t + 8 * vl),
      (P, P + 8 * il)] := by
    refine (mfTrans (mfTrans (mfTrans hA1 hQ1f) hA2) hQ2f).mono fun a n ho => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, -, -, -, -⟩ := sh_rd hE hS hF
  have r9 : m4.readLE (s.sp.toNat - 120) 8 = sh := by
    rw [hQ2f.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hA2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hQ1f.readLE _ _ (by have := hl.tw; simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hA1sh
  have hacc : m4.accessible (P + 8 * il) 8 true = true := by
    rw [hF.accessible, hS.mem.fr.accessible]
    exact Memory.accessible_mono _ (by rw [← hS.mem.fr.accessible]; exact hU.pacc) (by omega) (by omega)
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : m4.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hF.accessible, hS.mem.fr.accessible]; exact hw
  have hPa : (P + 8 * il) % 2 ^ 64 = P + 8 * il := Nat.mod_eq_of_lt (by omega)
  janus_run [hm, r1, r2, r3, r4, r5, r6, r7, r8, r9, hPa] until [aliasPt]
  rw [show P + il * 8 = P + 8 * il by omega]
  refine k _ ⟨rfl, rfl, ?g28, ?g29, ?g18, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmU, hUA, hS.ext2, hS.bud2, ?gs,
    hvv, hvt, huv, by simp only [Memory.regions_writeLE]; exact hreg4⟩
  case gs => have := (AsmDiv.clz_norm64 _ (by
      rcases hE.pre.vn with h | h
      · have := hl.v2; omega
      · exact h) (Memory.readLE_lt _ _ _)).1; omega
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18]

end FvModexp.Arm64.DivLarge
