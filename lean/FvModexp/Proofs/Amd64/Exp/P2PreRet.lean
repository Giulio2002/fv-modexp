import FvModexp.Proofs.Amd64.Exp.P2PreLJ

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the loop exit `i = len` → return (`+0x5ab`) (agent divmc s64; twin of
infra's `Arm64/Exp/P2PreRet`)

`headRet`: `HeadJ … len` — the test `i < len` fails (`+0x393`), `ADDQ $0xa8, SP; POPQ BP; RET`; the postcondition from
the context (`powers[j]` computed for every `j < len`, the whole budget `cost` spent).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem headRet {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State} (hkc : 4608 ≤ kc) :
    HeadJ impl R kc b L st pw pl ws lm x xl s pl := by
  intro S bp L1 b1 hpre hpc hfr h0 h2 hc hd _ _ _ _ hb
  have hf := pf_of hpre (by omega)
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hfr' := hfr
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr'
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hR64 := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hwm : S.mem.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  obtain ⟨e0, e1, -, -, -, -, -, -, e8, -, -⟩ := hc.sl
  have f144 : S.mem.readLE ((s.regs 4).toNat - 176 + 144) 8 = pl := by
    rw [show (s.regs 4).toNat - 176 + 144 = (s.regs 4).toNat - 32 by omega]; exact e8
  have h168 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) + 168#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h8 : BitVec.ofNat 64 ((s.regs 4).toNat - 8) + 8#64 = s.regs 4 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have t8 : (BitVec.ofNat 64 ((s.regs 4).toNat - 8)).toNat = (s.regs 4).toNat - 8 := tN (by omega)
  have hb' : b - cost pl lm + stkR (HP (stLen s.mem st) pl lm) S.mem st ≤
      b1 + stkR (HP (stLen s.mem st) pl lm) S.mem st := by simp only [cost]; omega
  unfold Goal
  janus64_run [f144, hwm, h168, h8, t8, e0, e1]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, bp, fun j hj => hd j hj, L1, b1 + stkR (HP (stLen s.mem st) pl lm) S.mem st,
    hc.le, hb', hc.inv, hc.scr, hc.sap, hc.sa, hc.fr, hc.lf, hc.ain, hc.bu⟩
  all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hx15 | rfl)

end FvModexp.Amd64.P2Pre
