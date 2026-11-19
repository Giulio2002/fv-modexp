import Janus

-- adapted from fv-uint256 lean/Fv256/Proofs/Common/UtilE.lean (`ensures_of_summary64`)

/-! # amd64: a `Summary` of an ABIInternal function gives its `Ensures` (Extracted-free) -/

namespace FvModexp.Asm

theorem ensures_of_summary64 {p : Janus.Amd64.Program} {entry : Nat} {args : List Janus.Amd64.W64}
    {spre pre : Janus.Amd64.State → Prop} {Q post : Janus.Amd64.State → Janus.Amd64.State → Prop}
    (hsum : Janus.Amd64.Tactic.Summary p entry spre Q)
    (hpre : ∀ ret s, Janus.Amd64.GoABI.RetAddr p ret →
      Janus.Amd64.GoABI.CallSetup (p.withExit ret) entry args s → pre s → spre s)
    (hpost : ∀ ret s s', Janus.Amd64.GoABI.RetAddr p ret →
      Janus.Amd64.GoABI.CallSetup (p.withExit ret) entry args s → pre s → Q s s' →
      Janus.Amd64.GoABI.ABIReturn s s' ∧ post s s') (hinv : Janus.Amd64.GoABI.Ensures.SetRetInv p entry args pre := by janus64_pre_setRet) :
    Janus.Amd64.GoABI.Ensures p entry args pre post := by
  refine Janus.Amd64.GoABI.Ensures.of_old hinv ?_
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.rip (hpre ret s hret hs hp)
  refine Janus.Amd64.GoABI.returns_of_steps (Janus.Amd64.Program.Steps.withExit hst hret.fetch_none) ?_
    (hpost ret s s' hret hs hp hq)
  rw [hr, Janus.Amd64.Tactic.retAddrOf, hs.ret]
  simp only [Janus.Amd64.Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hret.user (by decide))

end FvModexp.Asm
