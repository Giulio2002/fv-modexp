import FvModexp.Proofs.Amd64.NatQ.DrsAt
import FvModexp.Proofs.Amd64.NatQ.DrsFin

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): `len u < n` — nothing to do (natdiv.go:766-769)

From the dispatch: `TESTQ R8, R8; JE` (not taken, `len u > 0`), `CMPQ divRecursiveThreshold, R11; JG` (not taken,
`n ≥ 40`), `MOVQ R8, R13; SUBQ R11, R8; TESTQ R8, R8; JL 0x5ef9ff` (taken) and the epilogue. Twin of
Arm64/NatQ/DrsEntry.lean `pathC`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- `U < V` when the normalised `len u` is below `len v` (whose top word is not zero) -/
theorem u_lt_v {M : Memory} {up ul ul' vp vl : Nat} (hv1 : 1 ≤ vl) (htop : 2 ^ 63 ≤ M.readLE (vp + 8 * (vl - 1)) 8)
    (hlt : ul' < vl) (hU : natVal M up ul' = natVal M up ul) : natVal M up ul < natVal M vp vl := by
  have h1 := natVal_lt M up ul'
  have h3 := natVal_ge M vp vl hv1 (by omega)
  have h4 : 2 ^ (64 * ul') ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`len u < n`**: return at `0x5ef9ff` with `z = 0 = U / V`, `u = U = U mod V` -/
theorem pathC (impl : List Amd64.Segment) (R : RtInv) (a : Args) (s : State) (hE : Entry a s) {c : Nat}
    (hpre : DrsPreW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat a.ul.toNat a.uc.toNat
      a.vp a.vl a.vc s) (hW : 400 ≤ a.W) (P : State) (ul' : Nat)
    (hA : AtE2 s P a.qp.toNat a.ql.toNat a.qc.toNat a.st.toNat a.up.toNat ul' a.uc.toNat a.vp a.vl a.vc a.d.toNat)
    (hU : natVal s.mem a.up.toNat ul' = natVal s.mem a.up.toNat a.ul.toNat) (h0 : 0 < ul') (h40 : 40 ≤ a.vl)
    (hlt : ul' < a.vl) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P (fun s' => Kept s s' ∧
      DrsPostW R a.b a.L a.Hq c a.W a.qp.toNat a.ql.toNat a.st.toNat a.up.toNat a.ul.toNat a.vp a.vl s s') := by
  have hce := hpre.ce
  have hgl := hpre.gl
  have hv2 := hpre.v2
  have htop := hpre.vtop
  have hq0 := hpre.q0
  have hulc := hpre.ulc
  have huc := hpre.uc40
  have hvlc := hpre.vlc
  have hvc := hpre.vc40
  have hlt' := u_lt_v (by omega) htop hlt hU
  obtain ⟨hra, hx15, hdf, -⟩ := hE
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -⟩ := hce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, -, hth, -, -, -, hgacc, -, hgw, -⟩ := hgl
  have eg : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» = 0xb4ae88 := rfl
  simp only [RunIface.gA, eg, win, outside_cons, outside_nil, and_true] at hgw hgacc hth
  have hF := hA.fr
  have hth' : P.mem.readLE 0xb4ae88 8 = 40 := by
    rw [hF.fr.readLE _ _ (by simp only [fw, win, outside_cons, outside_nil, and_true]; omega)]; exact hth
  have hthA : P.mem.accessible 0xb4ae88 8 false = true := by
    rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)
  have h8 := hA.r8
  have h11 := hA.r11
  have hne : (BitVec.ofNat 64 ul' = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hsub : (BitVec.ofNat 64 ul' - BitVec.ofNat 64 a.vl).msb = true := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (show ul' < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a.vl < 2 ^ 64 by omega)]; omega
  have hpc := hA.pc
  have hx0 := hA.x15
  have hacc8 : P.mem.accessible ((s.regs 4).toNat - 8) 16 false = true := by
    rw [hF.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  janus64_run [h8, h11, hth', hne, hsub, BitVec.msb_eq_decide] until [epC]
  refine epi impl s _ epC (Or.inl rfl) rfl ?sp ?r14 ?fs ?df ?ra ?bp ?x hdf hra (by omega) (by omega) ?acc _
    fun s' ⟨e1, e2, e3, e4⟩ => ⟨e1, post_frame hpre hW (by rw [e4]; exact hF.fr) e2 e3 ?q ?u⟩
  case sp => first | exact hF.sp | (janus64_simp; exact hF.sp)
  case r14 => first | exact hF.r14 | (janus64_simp; exact hF.r14)
  case fs => first | exact hF.fs | (janus64_simp; exact hF.fs)
  case df => first | exact hF.df | (janus64_simp; exact hF.df)
  case ra => first | exact hF.ra | (janus64_simp; exact hF.ra)
  case bp => first | exact hF.bp | (janus64_simp; exact hF.bp)
  case x => first | (rw [hx0, hx15]) | (janus64_simp; rw [hx0, hx15])
  case acc => first | exact hacc8 | (janus64_simp; exact hacc8)
  case q => rw [hq0, Nat.div_eq_of_lt hlt']
  case u => exact (Nat.mod_eq_of_lt hlt').symm

end FvModexp.Amd64.Q.DivRec
