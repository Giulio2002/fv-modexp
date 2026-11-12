import FvModexp.Proofs.Arm64.Nat.MulLift
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.mul` (arm64): `len y = 0` (`m ≥ n = 0`) → `return z[:0]` (natmul.go:24-25)

`mpost_nil`: a path that writes only the window and returns `z[:0]` for a zero product satisfies `MPost`; `zero`:
the entry → `0x1bb120` → the return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (stackBack_keep)

set_option maxRecDepth 20000 in
theorem mpost_nil {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s s' : State}
    (hpre : MPre R b L W zp zc st xp xl xc yp yl yc s) (hF : MemFrame s.mem s'.mem (winA s W 88))
    (hxy : natVal s.mem xp xl * natVal s.mem yp yl = 0)
    (r0 : s'.regs 0 = BitVec.ofNat 64 zp) (r1 : s'.regs 1 = BitVec.ofNat 64 0) (r2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    MPost R b L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hce, -, -, -, -, ⟨-, -, ⟨hz40, hzl, hzw, -, -, -⟩, -⟩, hstk, -, hinv⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  obtain ⟨-, hstok, hstw, -⟩ := hstk
  have hzA := winA_of_win' hzw
  have hF' : MemFrame s.mem s'.mem (R.rt ++ winA s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
    hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2
  have hLF : ∀ ws, LiveFrame s.mem s'.mem L ws := fun ws => lf_win' ws hF hLs
  refine ⟨zp, 0, zc, r0, r1, r2, by rw [natVal_zero, hxy], Or.inl rfl, Nat.zero_le _, Nat.zero_le _, hz40, L, b,
    LiveExt.refl R L, Nat.sub_le _ _, inv_frame_winA hF hout (by omega) (by decide) hinv, ?_, Or.inl ⟨rfl, rfl⟩,
    fun h => absurd ⟨rfl, rfl⟩ h, ?_, stackBack_keep hstok hF (winA_of_win' hstw) (LiveExt.refl R L), hF', hLF _⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · intro h1 _ _
    refine ⟨rfl, rfl, Or.inr ⟨hxy, natVal_frame hF (hzA.of_sub (Nat.le_refl _) (by omega))⟩,
      hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2, hLF _⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zero (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bae70)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp)
    (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc) (h7 : s.regs 7 = yp) (h8 : s.regs 8 = yl) (h9 : s.regs 9 = yc)
    (hpre : MPre R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy : yl.toNat = 0) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) s fun s' =>
      Kept s s' ∧ MPost R b L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩, hmw, -, -, -,
    ⟨⟨-, -, hxl12, -⟩, -⟩, -⟩ := hpre'
  have hW : 4608 ≤ W := Nat.le_trans (mulW_ge _ _) hmw
  have hyl0 : yl = 0#64 := BitVec.eq_of_toNat_eq (by simp [hy])
  have hxy : natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat = 0 := by rw [hy]; simp
  subst hyl0
  by_cases hx0 : xl = 0#64
  · subst hx0
    janus_run
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_nil hpre ?qF hxy ?_ ?_ ?_⟩
    case qF => simp only [winA]; janus_frame
    all_goals janus_simp
  · have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; exact hx0
    janus_run [toInt_small xl (by omega), hx0']
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_nil hpre ?qF hxy ?_ ?_ ?_⟩
    case qF => simp only [winA]; janus_frame
    all_goals janus_simp

end FvModexp.Arm64.NatMul
