import FvModexp.Proofs.Amd64.Exp.LibN
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), stack given: `J2` = fn+0x19c → `nat.rem` entry | `J4` = fn+0x464 (agent expmc s66; twin of
`Arm64.ExpN.stk`)

nat.go:663-686 with `len m ≠ 0`, `stk ≠ nil` (`RSP = t - 0x108`): spills `R8 → t + 0x60`, `SI → t + 0x58` (`x`; the
`y == 1 && len m == 0` test falls through since `R11 = len m ≠ 0`), `R10` byte `→ t + 0x70`, `R9 → t + 0x68`,
`AX → t - 0x20` (reloaded), the defer flag byte `t - 0x9a` := 0; then `len y == 1 && y[0] == 1` → `z.rem(stk, x, m)`
(`m` stored to `[t - 0x108, t - 0xf0)`, `CALL` at fn+0x40a, return `remR` = fn+0x40f pushed at `t - 0x110`), else
`J4` (`TESTQ R11` of nat.go:693). Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `nat.rem`'s entry (`0x5edca0`) -/
abbrev remA : Nat := 6216864
/-- the return point of the `rem` call (`0x5e73af`) -/
abbrev remR : Nat := 6189999

/-- a read of exactly the bytes just written (the addresses equal up to arithmetic) -/
theorem rd_wr_eq {m : Janus.Arm64.Memory} {a b n v : Nat} (h : a = b) : (m.writeLE a n v).readLE b n = v % 256 ^ n := by
  subst h; exact Janus.Arm64.Memory.readLE_writeLE_self _ _ _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.unusedSimpArgs false in
theorem stk (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t yp yl mp n mc st : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hyl : yl < 2 ^ 64) (hn : n < 2 ^ 64) (hmp : mp < 2 ^ 64) (hst : st < 2 ^ 64) (hn0 : 0 < n) (hst0 : 0 < st)
    (hy0 : yl ≠ 0) (hyp : yp < 2 ^ 64) (hya : M.accessible yp 8 false = true)
    (hyo : yp + 8 ≤ t - 0x110 ∨ t + 0x78 ≤ yp) (r30 : M.readLE (t + 0x30) 8 = mc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6189372) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h12 : S.regs 12 = BitVec.ofNat 64 yp) (h15 : S.regs 15 = BitVec.ofNat 64 yl)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h13 : S.regs 13 = BitVec.ofNat 64 mp) (hmem : S.mem = M)
    (KR : yl = 1 → M.readLE yp 8 = 1 → ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 remA → S'.regs 4 = BitVec.ofNat 64 (t - 0x110) →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = S.regs 7 →
      S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x110, t - 0xf0), (t - 0x9a, t - 0x99), (t - 0x20, t - 0x18), (t + 0x58, t + 0x78)] →
      M'.regions = M.regions →
      M'.readLE (t - 0x110) 8 = remR → M'.readLE (t - 0x108) 8 = mp → M'.readLE (t - 0x100) 8 = n →
      M'.readLE (t - 0xf8) 8 = mc → M'.readLE (t - 0x9a) 1 = 0 →
      M'.readLE (t + 0x58) 8 = (S.regs 6).toNat → M'.readLE (t + 0x60) 8 = (S.regs 8).toNat →
      M'.readLE (t + 0x68) 8 = (S.regs 9).toNat → M'.readLE (t + 0x70) 1 = (S.regs 10).toNat % 256 →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KD : ¬(yl = 1 ∧ M.readLE yp 8 = 1) → ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 6190084 → S'.regs 4 = S.regs 4 →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = S.regs 7 →
      S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 →
      S'.regs 11 = S.regs 11 → S'.regs 12 = S.regs 12 → S'.regs 13 = S.regs 13 → S'.regs 15 = S.regs 15 →
      S'.regs 5 = S.regs 5 → S'.regs 2 = S.regs 2 →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x9a, t - 0x99), (t - 0x20, t - 0x18), (t + 0x58, t + 0x78)] → M'.regions = M.regions →
      M'.readLE (t - 0x9a) 1 = 0 →
      M'.readLE (t + 0x58) 8 = (S.regs 6).toNat → M'.readLE (t + 0x60) 8 = (S.regs 8).toNat →
      M'.readLE (t + 0x68) 8 = (S.regs 9).toNat → M'.readLE (t + 0x70) 1 = (S.regs 10).toNat % 256 →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have hy8 : M.readLE yp 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc8 : mc < 2 ^ 64 := r30 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have a30 : t - 0x108 + 0x138 = t + 0x30 := by omega
  have bn : (BitVec.ofNat 64 n = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  have bs : (BitVec.ofNat 64 st = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  subst hmem
  janus64_run [es1, a30, r30, bn, bs] until [remA, 6190084]
  · have e1 : yl = 1 := by omega
    have e2 : S.mem.readLE yp 8 = 1 := by omega
    refine KR e1 e2 _ _ ?ar0 ?ar1 ?ar2 ?ar3 ?ar4 ?ar5 ?ar6 ?ar7 ?ar8 ?ar9 ?ar10 ?ar11 ?ar12 ?ar13
      rfl ?amf ?arg ?aq0 ?aq1 ?aq2 ?aq3 ?aq4 ?aq5 ?aq6 ?aq7 ?aq8
    case amf => janus_frame
    case arg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case ar0 | ar1 | ar2 | ar3 | ar4 | ar5 | ar6 | ar7 | ar8 | ar9 |
        ar10 | ar11 | ar12 | ar13 => rfl
    all_goals (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h11, h13] <;> omega)
  · have e2 : ¬S.mem.readLE yp 8 = 1 := by omega
    refine KD (fun h => e2 h.2) _ _ ?br0 ?br1 ?br2 ?br3 ?br4 ?br5 ?br6 ?br7 ?br8 ?br9
      ?br10 ?br11 ?br12 ?br13 ?br14 ?br15 ?br16 ?br17 ?br18 ?br19
      rfl ?bmf ?brg ?bq0 ?bq1 ?bq2 ?bq3 ?bq4
    case bmf => janus_frame
    case brg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case br0 | br1 | br2 | br3 | br4 | br5 | br6 | br7 | br8 | br9 |
        br10 | br11 | br12 | br13 | br14 | br15 | br16 | br17 | br18 | br19 => rfl
    all_goals (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h11, h13] <;> omega)
  · have e1 : ¬yl = 1 := by omega
    refine KD (fun h => e1 h.1) _ _ ?cr0 ?cr1 ?cr2 ?cr3 ?cr4 ?cr5 ?cr6 ?cr7 ?cr8 ?cr9
      ?cr10 ?cr11 ?cr12 ?cr13 ?cr14 ?cr15 ?cr16 ?cr17 ?cr18 ?cr19
      rfl ?cmf ?crg ?cq0 ?cq1 ?cq2 ?cq3 ?cq4
    case cmf => janus_frame
    case crg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case cr0 | cr1 | cr2 | cr3 | cr4 | cr5 | cr6 | cr7 | cr8 | cr9 |
        cr10 | cr11 | cr12 | cr13 | cr14 | cr15 | cr16 | cr17 | cr18 | cr19 => rfl
    all_goals (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h11, h13] <;> omega)

end FvModexp.Amd64.ExpN
