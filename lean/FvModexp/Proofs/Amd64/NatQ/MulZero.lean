import FvModexp.Proofs.Amd64.NatQ.MulLift

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulZero.lean — TIGHT COSTS] `nat.mul` (amd64): `len y = 0` (`m ≥ n = 0`) → `return z[:0]` (natmul.go:24-25)

`mpost_nil`: a path that writes only the window and returns `z[:0]` for a zero product satisfies `MPost`; `zero`:
the entry `0x5f0840` (`CMPQ R8, R10; JL` not taken; `TESTQ R8, R8` / `TESTQ R10, R10; JE 0x5f0c19`) → the return.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (stackBack_keep inv_frame_win)

set_option maxRecDepth 20000 in
theorem mpost_nil {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s s' : State}
    (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s) (hF : MemFrame s.mem s'.mem (win s W 88))
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hxy : natVal s.mem xp xl * natVal s.mem yp yl = 0)
    (r0 : s'.regs 0 = BitVec.ofNat 64 zp) (r1 : s'.regs 3 = BitVec.ofNat 64 0) (r2 : s'.regs 1 = BitVec.ofNat 64 zc) :
    MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hce, -, -, -, -, ⟨-, -, ⟨hz40, hzl, hzw, -, -, -⟩, -⟩, hstk, ⟨-, hcost⟩, -, hinv⟩ := hpre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, hstok, hstw, -⟩ := hstk
  obtain ⟨-, -, eC⟩ := hdr_frame hF hstw
  have hF' : MemFrame s.mem s'.mem (R.rt ++ win s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
    hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2
  have hLF : ∀ ws, LiveFrame s.mem s'.mem L ws := fun ws => lf_win' ws hF hLs
  refine ⟨hfs, hdf, zp, 0, zc, r0, r1, r2, by rw [natVal_zero, hxy], Or.inl rfl, Nat.zero_le _, Nat.zero_le _, hz40,
    L, b, LiveExt.refl R L, by rw [stkR_congr eC]; omega, inv_frame_win hF hout (by omega) (by decide) hinv, ?_,
    Or.inl ⟨rfl, rfl⟩, fun h => absurd ⟨rfl, rfl⟩ h, ?_, stackBack_keep hstok hF hstw (LiveExt.refl R L), hF', hLF _⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · intro h1 _ _
    refine ⟨rfl, rfl, Or.inr ⟨hxy, natVal_frame hF (hzw.of_sub (Nat.le_refl _) (by omega))⟩,
      hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.1.2, hLF _⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zero (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0840)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hy1 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat) (hy2 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat)
    (hy3 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hy : yl.toNat = 0) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s fun s' =>
      Kept s s' ∧ MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hmw, -, -, -, ⟨⟨-, -, hxl12, -⟩, -⟩, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hxy : natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat = 0 := by rw [hy]; simp
  rw [hy] at hy2
  by_cases hx0 : xl = 0#64
  · subst hx0
    janus64_run [BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_nil hpre ?qF ?_ ?_ hxy ?_ ?_ ?_⟩
    case qF => simp only [win]; janus_frame
    all_goals janus64_simp
  · have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; exact hx0
    janus64_run [BitVec.msb_eq_decide, hx0']
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_nil hpre ?qF ?_ ?_ hxy ?_ ?_ ?_⟩
    case qF => simp only [win]; janus_frame
    all_goals janus64_simp

end FvModexp.Amd64.Q.NatMul
