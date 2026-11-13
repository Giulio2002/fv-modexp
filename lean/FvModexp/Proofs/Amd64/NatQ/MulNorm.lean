import FvModexp.Proofs.Amd64.NatQ.MulRel
import FvModexp.Proofs.Amd64.NatQ.SqrNorm

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulNorm.lean — TIGHT COSTS] `nat.mul` (amd64): the two inlined `z.norm()` loops

`for i > 0 && z[i-1] == 0 { i-- }; return z[0:i]`; the result is stored to `0x98..0xaf(SP')` (`SP' = RSP - 256`, i.e.
`[RSP - 104, RSP - 80)`) and returned in `AX, BX, CX`. `normA` (after `basicMul`, head `0x5f0c8b`: `AX = p`, `BX = i`,
cap reloaded from `0x58(SP') = RSP - 168`) returns; `normB` (after `karatsuba` / the chunk loop, head `0x5f0e14`:
`SI = p`, `BX = i`, `AX` = the defer bits) stops at `0x5f0e47` (the deferred-call tests); `retB0`: from there with no
deferred call, the return.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (natVal_drop_zero)

abbrev hnormA : Nat := 0x5f0c8b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normA (impl : List Amd64.Segment) (s : State) (M : Memory) (p c n0 V : Nat)
    (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), MemFrame M s'.mem [((s.regs 4).toNat - 104, (s.regs 4).toNat - 80)] →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 n' → s'.regs 1 = BitVec.ofNat 64 c →
      s'.fsBase = s.fsBase → s'.df = s.df → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hr3 : M.readLE ((s.regs 4).toNat - 168) 8 = c)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 256 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 256) 264 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hnormA → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 4 = s.regs 4 - 256#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mem = M →
      natVal M p i = V →
      ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr1, hr2, hr3, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ 0 (by janus_frame) ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)⟩
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hdf | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc hi0 hp0 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr1, hr2, hr3, key, BitVec.msb_eq_decide] until [hnormA]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by janus64_simp) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    case hq =>
      rename_i hz _
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin _ (i + 1) (by janus_frame) ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)⟩
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hdf | exact hx15 | omega

abbrev hnormB : Nat := 0x5f0e14

/-- the state at the deferred-call tests `0x5f0e47` after `normB` -/
structure AtB (s S : State) (M : Memory) (p c n' bits : Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 0x5f0e47
  r0 : S.regs 0 = BitVec.ofNat 64 bits
  sp : S.regs 4 = s.regs 4 - 256#64
  g : S.regs 14 = s.regs 14
  bp : S.regs 5 = s.regs 4 - 8#64
  x15 : S.xmm 15 = s.xmm 15
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  fr : MemFrame M S.mem [((s.regs 4).toNat - 104, (s.regs 4).toNat - 80)]
  m152 : S.mem.readLE ((s.regs 4).toNat - 104) 8 = p
  m160 : S.mem.readLE ((s.regs 4).toNat - 96) 8 = n'
  m168 : S.mem.readLE ((s.regs 4).toNat - 88) 8 = c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem normB (impl : List Amd64.Segment) (s : State) (M : Memory) (p c n0 V bits : Nat) (Q : State → Prop)
    (hfin : ∀ (S' : State) (n' : Nat), AtB s S' M p c n' bits → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibMul.program.link impl) (retAddrOf s) S' Q)
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr3 : M.readLE ((s.regs 4).toNat - 168) 8 = c) (hbits : bits < 256)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 256 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 256) 264 true = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 hnormB → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 6 = BitVec.ofNat 64 p → S.regs 0 = BitVec.ofNat 64 bits → S.regs 4 = s.regs 4 - 256#64 →
      S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase →
      S.df = s.df → S.mem = M → natVal M p i = V →
      ReachesRet (LibMul.program.link impl) (retAddrOf s) S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc hi0 hp0 hb0 hsp h14 h5 hx15 hfs hdf hm hv
    janus64_run [hm, hr3, BitVec.msb_eq_decide] until [0x5f0e47]
    refine hfin _ 0 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by janus_frame, ?_, ?_, ?_⟩ (Nat.zero_le _) (by simpa using hv)
      (Or.inl rfl)
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hdf | exact hx15 | omega
  | succ i ih =>
    intro S hi hpc hi0 hp0 hb0 hsp h14 h5 hx15 hfs hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, hr3, key, BitVec.msb_eq_decide] until [hnormB, 0x5f0e47]
    all_goals first
      | (have hz := hbr
         rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
         exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
           (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp; exact hfs) (by janus64_simp) rfl
           ((natVal_drop_zero hz).symm.trans hv))
      | (rename_i hz
         rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
         refine hfin _ (i + 1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by janus_frame, ?_, ?_, ?_⟩ hi hv (Or.inr hz)
         all_goals try janus64_simp
         all_goals first | exact hfs | exact hdf | exact hx15 | omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- no deferred call (`bits = 0`): reload the result and return -/
theorem retB0 (impl : List Amd64.Segment) (s S : State) (M : Memory) (p c n' : Nat) (hB : AtB s S M p c n' 0)
    (hr1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hr2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp0 : 256 ≤ (s.regs 4).toNat) (hsp1 : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hsacc : M.accessible ((s.regs 4).toNat - 256) 264 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hp : p < 2 ^ 64) (hn : n' < 2 ^ 64) (hc : c < 2 ^ 64) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ s'.mem = S.mem ∧
      s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 n' ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
      s'.fsBase = s.fsBase ∧ s'.df = s.df := by
  obtain ⟨hpc, h0, hsp, h14, h5, hx15, hfs, hdf, hF, m1, m2, m3⟩ := hB
  have e1 : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hr1
  have e2 : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hr2
  have ea : S.mem.accessible ((s.regs 4).toNat - 256) 264 true = true := by rw [hF.accessible]; exact hsacc
  clear hF
  janus64_run [e1, e2, m1, m2, m3, BitVec.msb_eq_decide]
  all_goals try janus64_simp
  all_goals first
    | rfl | exact hfs | exact hdf | omega
    | (refine ⟨⟨?_, ?_, ?_, ?_⟩, hfs⟩ <;> (try janus64_simp) <;> first | exact h14 | exact hx15 | rfl)

end FvModexp.Amd64.Q.NatMul
