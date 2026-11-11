import FvModexp.Proofs.Amd64.Nat.LibMulAddWW
import FvModexp.Proofs.Amd64.Nat.NatAddMid
import FvModexp.Proofs.Amd64.MulAddVWWSum

/-!
# `nat.mulAddWW` (go-bigmodexpfix natmul.go:136), amd64: statement, callee, segment-boundary facts

The amd64 twin of `FvModexp.Arm64.MulAddWW` (same Go source; `setWord`, `make`, `norm` inlined). Arguments
`z = (AX, BX, CX)`, `x = (DI, SI, R8)`, `y = R9`, `r = R10`; results `(AX, BX, CX)`.
Frame `PUSHQ BP; SUBQ $0x60, SP` (entry `RSP`, return address at `RSP`, saved `RBP` at `RSP - 8`, `RSP' = RSP - 104`):
locals `0x48(RSP') = RSP - 32` (cap), `0x50(RSP') = RSP - 24` (`m + 1`), `0x58(RSP') = RSP - 16` (p); spills
`0x70, 0x88, 0x90, 0x98, 0xa0, 0xa8(RSP')` = `RSP + 8, 32, 40, 48, 56, 64` (`above = 72`). Calls (callee `RSP = RSP - 112`):
`runtime.makeslice` (contract stack 4096: `stk = 112 + 4096 = 4208`) and `mulAddVWW.abi0` (frame words
`0 … 0x38(RSP')`, result `0x40(RSP') = RSP - 40`; afterwards `XORPS X15, X15; MOVQ FS:-8, R14`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

namespace FvModexp.Amd64.MulAddWW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mulAddWW"
def vwwFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.mulAddVWW.abi0"
def names : List String := LibMulAddWW.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- The capacity `mulAddWW` needs: `m + 1` (`make(m + 1)`), or `setWord(r)`'s `1` (`0` for `r = 0`). -/
@[reducible] def need (xl y r : BitVec 64) : Nat :=
  if xl.toNat = 0 ∨ y.toNat = 0 then (if r.toNat = 0 then 0 else 1) else xl.toNat + 1

/-- The precondition (the one `makeslice` request when `z` is too small). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4208 72 ∧ Outside wordT 16 R.rt ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s 4208 72) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4208 72) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl y r → R.ok (cA "runtime.makeslice") [wordT, need xl y r, makeCap (need xl y r)] ∧
      makeCost (need xl y r) ≤ b)

/-- The postcondition: a normalised nat `(p', n', c')` holding `X·y + r`, `z`'s array or a fresh one. -/
@[reducible] def PostI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = n' ∧ (s'.regs 1).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat + 1 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (need xl y r) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- the postcondition (AMD64 DF CONVENTION: `s'.df = s.df`) -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = n' ∧ (s'.regs 1).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat + 1 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (need xl y r) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- The registers every path keeps. -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.df = false

/-- The entry state. -/
@[reducible] def Entry (s : State) (zp zl zc xp xl xc y r : BitVec 64) : Prop :=
  s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn) ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧
    s.regs 6 = xl ∧ s.regs 8 = xc ∧ s.regs 9 = y ∧ s.regs 10 = r

/-! ## The callee `mulAddVWW.abi0`, moved into the restricted program -/

set_option maxRecDepth 100000 in
theorem codeIn_vww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.MulAddVWWAmd64.program (LibMulAddWW.program.link impl) := by
  rw [LibMulAddWW.eq_only]
  exact Callees.codeIn_single hap (seg := Extracted.seg62) rfl
    (List.getElem_mem (l := Extracted.program.segments) (n := 62) (by decide)) (by decide)

/-- = asm `MulAddVWWSum.Q` (`lv` = `natVal`), reducible so that `janus64_run` destructures it. -/
abbrev VQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      (natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) *
          s.mem.readLE ((s.regs 4).toNat + 56) 8 + s.mem.readLE ((s.regs 4).toNat + 64) 8) %
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  m.readLE ((s.regs 4).toNat + 72) 8 =
      (natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) *
          s.mem.readLE ((s.regs 4).toNat + 56) 8 + s.mem.readLE ((s.regs 4).toNat + 64) 8) /
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 72, (s.regs 4).toNat + 80)]

/-- `mulAddVWW.abi0` with the runtime invariant, the stack guard and the TLS slot carried over. -/
abbrev VLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  MulAddVWWSum.Pre s ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
    Outside ((s.regs 4).toNat + 72) 8 R.rt ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      ((s.regs 14).toNat + 16) 8 ∧
    Apart ((s.regs 4).toNat + 72) 8 ((s.regs 14).toNat + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.fsBase.toNat - 8) 8 ∧
    Apart ((s.regs 4).toNat + 72) 8 (s.fsBase.toNat - 8) 8

abbrev VLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  VQ s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8

theorem vww_live (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibMulAddWW.program.link impl) (segAddr Extracted.program vwwFn) (VLPre R b L) (VLQ R b L) := by
  have he : segAddr Extracted.program vwwFn = FvModexp.Lib.MulAddVWWAmd64.entry := by decide
  rw [he]
  have h0 := Summary.of_codeIn64 (codeIn_vww impl hap) MulAddVWWSum.mulAddVWW_summary
  refine Summary0.mono (Callees.Summary0.live h0 (fun s => [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 72, (s.regs 4).toNat + 80)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2, ha3, ha4⟩
  refine ⟨hp, hi, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega
  · simp only [Outside, and_true]; unfold Apart at ha3 ha4; omega

/-! ## The facts after `z.make(m + 1)` (`Mid`) -/

/-- The join of the reuse and allocation paths of `z.make(m + 1)` (`CMPQ SI, CX`). -/
abbrev hMid : Nat := segAddr Extracted.program fn + 0xae

/-- The segment-boundary facts after the result array `(p, c)` is chosen. -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4208 < (s.regs 4).toNat
  tlsg : TlsG s
  trt : Outside (s.fsBase.toNat - 8) 8 R.rt
  tw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 4208) (4208 + 72)
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  g48 : (s.regs 14).toNat + 24 ≤ 2 ^ 48
  al : (s.regs 4).toNat % 8 = 0
  sp0 : 4208 ≤ (s.regs 4).toNat
  sp1 : (s.regs 4).toNat + 72 ≤ 2 ^ 48
  wrt : Outside ((s.regs 4).toNat - 4208) (4208 + 72) R.rt
  gw : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4208) (4208 + 72)
  grt : Outside ((s.regs 14).toNat + 16) 8 R.rt
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  xl40 : xl.toNat < 2 ^ 40
  -- frame words and spills
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sm : M.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat
  sm1 : M.readLE ((s.regs 4).toNat - 24) 8 = xl.toNat + 1
  sacc : M.accessible ((s.regs 4).toNat - 4208) (4208 + 72) true = true
  gacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8
  tacc : M.accessible (s.fsBase.toNat - 8) 8 false = true
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  -- the result array
  cap : xl.toNat + 1 ≤ c
  c41 : c < 2 ^ 41
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) ((s.regs 4).toNat - 4208) (4208 + 72)
  pg : Apart p (8 * c) ((s.regs 14).toNat + 16) 8
  pf : Apart p (8 * c) (s.fsBase.toNat - 8) 8
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  -- the operand
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  xw : Apart xp.toNat (8 * xl.toNat) ((s.regs 4).toNat - 4208) (4208 + 72)
  -- runtime
  ext : LiveExt R L L'
  bud : b - makeCost (xl.toNat + 1) ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  lsep : ∀ r ∈ L, Outside r.1 (r.2 - r.1) (win s 4208 72)
  mf : MemFrame s.mem M (R.rt ++ win s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- The stack ranges and array parts the code after `Mid` writes. -/
def WsOK (s : State) (p c : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ (((s.regs 4).toNat - 4208 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 24) ∨
    ((s.regs 4).toNat - 16 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 8) ∨ (p ≤ r.1 ∧ r.2 ≤ p + 8 * c))

/-- **A write without allocation keeps `Mid`** (stack stores, `mulAddVWW.abi0`, `z[m] = c`). -/
theorem Mid.frame0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) {M2 : Memory} {ws : List (Nat × Nat)}
    (hws : WsOK s p c ws) (hf : MemFrame M M2 ws) :
    Mid R b L zp zc xp xl s p c L' b' M2 := by
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hsp0 := h.sp0; have htw := h.tw; have hpf := h.pf
  unfold Apart at hpw hgw hpg htw hpf
  have rd : ∀ a, ((s.regs 4).toNat - 24 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 16 ∨
      (s.regs 4).toNat - 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 72) → M2.readLE a 8 = M.readLE a 8 := by
    intro a ha
    refine hf.readLE a 8 (outside_of_forall fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  have hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M2) := by
    refine RtInv.inv_frame' hf (fun r hr => ?_) h.inv
    have h0 := (hws r hr).1
    rcases (hws r hr).2 with h' | h' | h'
    · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
    · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
    · exact (h.pheld.sub h'.1 (by omega)).symm
  refine { h with
      lr := by rw [rd _ (by omega)]; exact h.lr
      fp := by rw [rd _ (by omega)]; exact h.fp
      sm := by rw [rd _ (by omega)]; exact h.sm
      sm1 := by rw [rd _ (by omega)]; exact h.sm1
      sacc := by rw [hf.accessible]; exact h.sacc
      gacc := by rw [hf.accessible]; exact h.gacc
      grd := ?_
      tacc := by rw [hf.accessible]; exact h.tacc
      tls := ?_
      pacc := by rw [hf.accessible]; exact h.pacc
      xacc := by rw [hf.accessible]; exact h.xacc
      inv := hinv
      mf := ?_
      lf := ?_ }
  · rw [← h.grd]
    refine hf.readLE _ _ (outside_of_forall fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · rw [← h.tls]
    refine hf.readLE _ _ (outside_of_forall fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · refine h.mf.trans (hf.widen R.rt) fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz⟩ := ho
    refine ⟨hrt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h'
    · omega
    · omega
    · rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
      · omega
      · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hf.readLE a n (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have hsep := h.lsep q hq
      simp only [win, outside_cons, outside_nil, and_true] at hsep hz
      rcases (hws r hr).2 with h' | h' | h'
      · omega
      · omega
      · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
        · omega
        · have := hap q hq; unfold Apart at this; omega

/-- **The postcondition** from `Mid` at the return (`s'.mem = M`, result `(p, n', c)`). -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {y r : BitVec 64}
    {s : State} {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0) (s' : State) (n' : Nat)
    (hm : s'.mem = M) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 3).toNat = n') (h2 : (s'.regs 1).toNat = c)
    (hfs : s'.fsBase = s.fsBase) (hn : n' ≤ xl.toNat + 1)
    (hv : natVal M p n' = natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat) (hnorm : NatNorm M p n') :
    PostI R b L zp zc xp xl y r s s' := by
  subst hm
  have hneed : need xl y r = xl.toNat + 1 := by unfold need; rw [if_neg (by omega)]
  refine ⟨hfs, p, n', c, h0, h1, h2, hv, hnorm, by have := h.cap; omega, hn, L', b', h.ext, ?_, h.inv,
    fun _ => ⟨h.p8, h.pheld, h.pacc, h.p48⟩, h.ror, h.mf, h.lf⟩
  rw [hneed]; exact h.bud

end FvModexp.Amd64.MulAddWW
