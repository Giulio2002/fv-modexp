import FvModexp.Proofs.Amd64.Exp.NEpi
import FvModexp.Proofs.Amd64.Exp.NNilTE

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the flag-1 epilogue code (agent expmc s74; twin of `Arm64.ExpN.epi1s/epi1c/epi1r`,
template top's Amd64/NatQ/DivMEpi.lean)

From a callee return point `r` (`RetPt`, `RSP = t - 0x108`):
* `epi1a`: the result stores (`RAX, RBX, RCX` → `[t - 0x58, t - 0x40)`), the defer flag byte `t - 0x9a` = 1 (`JE` not
  taken), `MOVB $0, t - 0x99`, `RDX := [t - 0x10]` (= `t - 0x30`, the closure record), `RAX := [RDX]` (=
  `deferwrap1`), `CALL AX` — stops at the closure entry (return `q`, `DwRet r q`, pushed at `t - 0x110`).
* `epi1b`: the closure call (any `Summary` of `deferwrap1` on `LibN`), the result reloads, `ADDQ $0x100, SP; POPQ BP;
  RET`. Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- the return point of the closure call after the callee return point `r` (`r + 0x34`; `r + 0x38` after
`expNNSlow`: a `NOPL` pads that epilogue) -/
def dwRet (r : Nat) : Nat := if r = 6190463 then r + 0x38 else r + 0x34

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- result stores, flag test, closure call: `r` → `deferwrap1`'s entry -/
theorem epi1a (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t r : Nat) (M : Janus.Arm64.Memory) (hr : RetPt r)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x118 true = true)
    (mfl : M.readLE (t - 0x9a) 1 = 1) (mrc : M.readLE (t - 0x10) 8 = t - 0x30) (mdw : M.readLE (t - 0x30) 8 = dwA)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 r) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108)) (hmem : S.mem = M)
    (k : ∀ (S2 : State), S2.rip = BitVec.ofNat 64 dwA →
      S2.regs 4 = BitVec.ofNat 64 (t - 0x110) →
      S2.regs 2 = BitVec.ofNat 64 (t - 0x30) → S2.regs 5 = S.regs 5 → S2.regs 14 = S.regs 14 →
      S2.xmm 15 = S.xmm 15 → S2.fsBase = S.fsBase → S2.df = S.df →
      MemFrame M S2.mem [(t - 0x110, t - 0x108), (t - 0x99, t - 0x98), (t - 0x58, t - 0x40)] →
      S2.mem.regions = M.regions → S2.mem.readLE (t - 0x110) 8 = dwRet r →
      S2.mem.readLE (t - 0x58) 8 = (S.regs 0).toNat → S2.mem.readLE (t - 0x50) 8 = (S.regs 3).toNat →
      S2.mem.readLE (t - 0x48) 8 = (S.regs 1).toNat → S2.mem.readLE (t - 0x99) 1 = 0 →
      Reaches ((LibN.program.link impl).withExit ret0) S2 Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have a6e : t - 0x108 + 0x6e = t - 0x9a := by omega
  have a6f : t - 0x108 + 0x6f = t - 0x99 := by omega
  have ab0 : t - 0x108 + 0xb0 = t - 0x58 := by omega
  have ab8 : t - 0x108 + 0xb8 = t - 0x50 := by omega
  have ac0 : t - 0x108 + 0xc0 = t - 0x48 := by omega
  have af8 : t - 0x108 + 0xf8 = t - 0x10 := by omega
  have rd : ∀ (m : Janus.Arm64.Memory) (a b c : Nat) {x k : Nat}, (x + k ≤ t - 0x58 ∨ t - 0x40 ≤ x) →
      (((m.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE x k = m.readLE x k := by
    intro m a b c x k h
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have mfl' : ∀ a b c : Nat, (((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).readLE
      (t - 0x9a) 1 = 1 := fun a b c => (rd M a b c (by omega)).trans mfl
  have mrc' : ∀ a b c : Nat, ((((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).writeLE
      (t - 0x99) 1 0).readLE (t - 0x10) 8 = t - 0x30 := fun a b c => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact (rd M a b c (by omega)).trans mrc
  have mdw' : ∀ a b c : Nat, ((((M.writeLE (t - 0x58) 8 a).writeLE (t - 0x50) 8 b).writeLE (t - 0x48) 8 c).writeLE
      (t - 0x99) 1 0).readLE (t - 0x30) 8 = 6191584 := fun a b c => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact (rd M a b c (by omega)).trans mdw
  have ht30 : (t - 0x30) % 2 ^ 64 = t - 0x30 := Nat.mod_eq_of_lt (by omega)
  subst hmem
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    janus64_run [es1, a6e, a6f, ab0, ab8, ac0, af8, mfl', mrc', mdw', ht30] until [dwA]
    refine k _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus_frame) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp only [Janus.Arm64.Memory.regions_writeLE]; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rd_wr_eq,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rd_wr_eq,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; exact Nat.mod_eq_of_lt (BitVec.isLt _))
      | (janus64_simp; done)
      | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the closure call and the return: `deferwrap1`'s entry → expNN's return -/
theorem epi1b (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    {preD : State → Prop} {postD : State → State → Prop}
    (hD : Summary (LibN.program.link impl) dwA preD postD) (F : State → Prop) (t r : Nat) (hr : RetPt r)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 dwA) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x110))
    (hra : S.mem.readLE (t - 0x110) 8 = dwRet r) (hpre : preD S)
    (hK : ∀ s3 : State, postD S s3 → s3.mem.regions = S.mem.regions →
      s3.regs 4 = S.regs 4 + 8#64 ∧ s3.mem.accessible (t - 0x108) 0x110 true = true ∧
      s3.mem.readLE t 8 = ret0 ∧
      ∀ s4 : State, s4.regs 4 = BitVec.ofNat 64 (t + 8) →
        s4.regs 0 = BitVec.ofNat 64 (s3.mem.readLE (t - 0x58) 8) →
        s4.regs 3 = BitVec.ofNat 64 (s3.mem.readLE (t - 0x50) 8) →
        s4.regs 1 = BitVec.ofNat 64 (s3.mem.readLE (t - 0x48) 8) →
        s4.regs 5 = BitVec.ofNat 64 (s3.mem.readLE (t - 8) 8) →
        s4.regs 14 = s3.regs 14 → s4.xmm 15 = s3.xmm 15 → s4.fsBase = s3.fsBase → s4.df = s3.df →
        s4.mem = s3.mem → F s4) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  refine Reaches.call_regions (hD.withExit hret) hpc hpre fun s3 hpc3 hpost hrg3 => ?_
  obtain ⟨e4, hacc3, hrv, K⟩ := hK s3 hpost hrg3
  have hS4 : (S.regs 4).toNat = t - 0x110 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hpc3' : s3.rip = BitVec.ofNat 64 (dwRet r) := by rw [hpc3, retAddrOf_eq, hS4, hra]
  have h4 : s3.regs 4 = BitVec.ofNat 64 (t - 0x108) := by
    rw [e4, hsp]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es1 : BitVec.ofNat 64 (t - 0x108) + 256#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ab0 : t - 0x108 + 0xb0 = t - 0x58 := by omega
  have ab8 : t - 0x108 + 0xb8 = t - 0x50 := by omega
  have ac0 : t - 0x108 + 0xc0 = t - 0x48 := by omega
  clear hpc3 e4 hpost hpre
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [dwRet, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceAdd] at hpc3'
  all_goals
    janus64_run [es1, es2, es3, ab0, ab8, ac0, hrv]
    refine K _ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl rfl
    all_goals first | rfl | (janus64_simp; done)

end FvModexp.Amd64.ExpN
