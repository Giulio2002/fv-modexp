import FvModexp.Proofs.Amd64.Nat.LibDivW
import FvModexp.Proofs.Amd64.Nat.NatAddMid
import FvModexp.Proofs.Amd64.Nat.DivWVW

set_option autoImplicit false

/-!
# `nat.divW` (go-bigmodexpfix natdiv.go:550), amd64: statement, callee, segment-boundary facts

See the arm64 twin for the Go source. Arguments `AX, BX, CX = z`, `DI, SI, R8 = x`, `R9 = y`; results
`AX, BX, CX = q`, `DI = r`. Frame `PUSHQ BP; SUBQ $0x78, SP` (entry `RSP`, return address at `RSP`, saved `RBP` at
`RSP - 8`, `RSP' = RSP - 128`); spills `0x88, 0xa0 … 0xb8(RSP')` = `RSP + 8, 32 … 56` (`above = 64`); locals of the
`divWVW` path `0x40, 0x48, 0x68(RSP')` = `RSP - 64` (m), `RSP - 56` (cap), `RSP - 24` (p); of the `set` path
`0x58, 0x60, 0x70(RSP')` = `RSP - 40, -32, -16`. Calls at `RSP_c = RSP - 136`: `runtime.makeslice`, `runtime.memmove`
(contract stack 4096: `stk = 136 + 4096 = 4232`), `divWVW` (asm's summary, `win 64 72`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

namespace FvModexp.Amd64.DivW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divW"
def names : List String := LibDivW.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- The precondition (as arm64; written arrays also apart from the TLS slot). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4232 64 ∧ Outside wordT 16 R.rt ∧ y.toNat ≠ 0 ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4232 64)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧
    Outside xp.toNat (8 * xl.toNat) (win s 4232 64) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k]) ∧
    (xl.toNat = 0 → y.toNat = 1 → zp = xp ∨
      (s.mem.accessible zp.toNat 0 true = true ∧ zp.toNat ≤ 2 ^ 48 ∧ Held R L zp.toNat 0 ∧
        Outside zp.toNat 0 (win s 4232 64)))

/-- The postcondition (`AX, BX, CX = q`, `DI = r`). -/
@[reducible] def PostI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = n' ∧ (s'.regs 1).toNat = c' ∧
    (s'.regs 7).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat / y.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost xl.toNat ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨
        (0 < xl.toNat ∧ xl.toNat ≤ c' ∧ c' ≤ xl.toNat + 4 ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4232 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- the postcondition (AMD64 DF CONVENTION: `s'.df = s.df`) -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = n' ∧ (s'.regs 1).toNat = c' ∧
    (s'.regs 7).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat / y.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost xl.toNat ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨
        (0 < xl.toNat ∧ xl.toNat ≤ c' ∧ c' ≤ xl.toNat + 4 ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4232 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- The registers every path keeps. -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.df = false

/-- The entry state. -/
@[reducible] def Entry (s : State) (zp zl zc xp xl xc y : BitVec 64) : Prop :=
  s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn) ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧
    s.regs 6 = xl ∧ s.regs 8 = xc ∧ s.regs 9 = y

/-! ## The callee `divWVW`, moved into the restricted program -/

theorem Ensures.toSummaryRegs8 {p0 P : Amd64.Program} {entry : Nat}
    {pre : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State → Prop}
    {post : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State →
      State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7]
      (pre a0 a1 a2 a3 a4 a5 a6 a7) (post a0 a1 a2 a3 a4 a5 a6 a7))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧ s.df = false ∧
        pre (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        post (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) s s') := by
  intro s hpc ⟨hret, hz, hdf, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9)
    (s.regs 10)) hx (by simp [numIntRegs]) hc s hpc ⟨hret, hz, by simp [ArgsFrom64, argReg, intArgRegs], hdf, hpre⟩

set_option linter.defProp false in
/-- `divWVW`'s `ens` as a summary inside `LibDivW.program.link impl`. -/
def dvw (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :=
  Ensures.toSummaryRegs8 (fun zp zl zc xn xp xl xc y => DivWVW.ens impl hap R b L zp zl zc xn xp xl xc y)
    (A64.noExit_restrict64 hap DivWVW.names)
    (show CodeIn64 ((Extracted.program.onlySegments DivWVW.names).link impl) (LibDivW.program.link impl) by
      rw [LibDivW.eq_only]; exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide)))

/-! ## The facts after `z.make(m)` (`Mid`), shared by the `divWVW` path and the `set` path -/

structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory) : Prop where
  gok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4232 < (s.regs 4).toNat
  tlsg : TlsG s
  trt : Outside (s.fsBase.toNat - 8) 8 R.rt
  tw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 4232) (4232 + 64)
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  g48 : (s.regs 14).toNat + 24 ≤ 2 ^ 48
  al : (s.regs 4).toNat % 8 = 0
  sp0 : 4232 ≤ (s.regs 4).toNat
  sp1 : (s.regs 4).toNat + 64 ≤ 2 ^ 48
  wrt : Outside ((s.regs 4).toNat - 4232) (4232 + 64) R.rt
  gw : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4232) (4232 + 64)
  grt : Outside ((s.regs 14).toNat + 16) 8 R.rt
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  xl40 : xl.toNat < 2 ^ 40
  x0 : 0 < xl.toNat
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sacc : M.accessible ((s.regs 4).toNat - 4232) (4232 + 64) true = true
  gacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8
  tacc : M.accessible (s.fsBase.toNat - 8) 8 false = true
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  cap : xl.toNat ≤ c
  c41 : c < 2 ^ 41
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) ((s.regs 4).toNat - 4232) (4232 + 64)
  pg : Apart p (8 * c) ((s.regs 14).toNat + 16) 8
  pf : Apart p (8 * c) (s.fsBase.toNat - 8) 8
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  xheld : Held R L' xp.toNat (8 * xl.toNat)
  xw : Apart xp.toNat (8 * xl.toNat) ((s.regs 4).toNat - 4232) (4232 + 64)
  ext : LiveExt R L L'
  bud : b - makeCost xl.toNat ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4232 64)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨
    (0 < xl.toNat ∧ xl.toNat ≤ c ∧ c ≤ xl.toNat + 4 ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s 4232 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)]
  mv : ∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k]

/-- The ranges the code after `Mid` (and its callees) may write: the window except the saved `RBP` and the return
address, and the result array. -/
def WsOK (s : State) (p c : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ (((s.regs 4).toNat - 4232 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 8) ∨
    ((s.regs 4).toNat + 8 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 64) ∨ (p ≤ r.1 ∧ r.2 ≤ p + 8 * c))

theorem Mid.frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) {M2 : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    {L'' : List (Nat × Nat)} {b'' : Nat} (hws : WsOK s p c ws) (hf : MemFrame M M2 (R.rt ++ ws))
    (hl : LiveFrame M M2 L' ws)
    (hext : LiveExt R L' L'') (hb : b' ≤ b'') (hinv : R.inv b'' L'' (s.regs 14).toNat (view R.rt L'' M2)) :
    Mid R b L zp zc xp xl s p c L'' b'' M2 := by
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hsp0 := h.sp0
  unfold Apart at hpw hgw hpg
  have key : ∀ a n, (s.regs 4).toNat - 4232 ≤ a → a + n ≤ (s.regs 4).toNat + 64 →
      (∀ r ∈ ws, a + n ≤ r.1 ∨ r.2 ≤ a) → Outside a n (R.rt ++ ws) := by
    intro a n h1 h2 h3
    simp only [outside_append]
    exact ⟨h.wrt.of_sub h1 (by omega), outside_of_forall h3⟩
  have rd : ∀ a, (s.regs 4).toNat - 8 ≤ a → a + 8 ≤ (s.regs 4).toNat + 8 → M2.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hf.readLE a 8 (key a 8 (by omega) (by omega) fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  refine { h with
      lr := by rw [rd _ (by omega) (by omega)]; exact h.lr
      fp := by rw [rd _ (by omega) (by omega)]; exact h.fp
      sacc := by rw [hf.accessible]; exact h.sacc
      gacc := by rw [hf.accessible]; exact h.gacc
      grd := ?_
      tacc := by rw [hf.accessible]; exact h.tacc
      tls := ?_
      pacc := by rw [hf.accessible]; exact h.pacc
      pheld := hext.held h.pheld
      xacc := by rw [hf.accessible]; exact h.xacc
      xheld := hext.held h.xheld
      ext := h.ext.trans hext
      bud := Nat.le_trans h.bud hb
      inv := hinv
      lsep := ?_
      mf := ?_
      lf := ?_ }
  · rw [← h.grd]
    refine hf.readLE _ _ ?_
    simp only [outside_append]
    refine ⟨h.grt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · rw [← h.tls]
    have htw := h.tw; have hpf := h.pf
    unfold Apart at htw hpf
    refine hf.readLE _ _ ?_
    simp only [outside_append]
    refine ⟨h.trt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · intro r hr
    obtain ⟨ns, rfl, hn, -⟩ := hext
    rcases List.mem_append.1 hr with hr | hr
    · exact h.lsep r hr
    · have hin := (hn r hr).1
      have hw := h.wrt
      simp only [win, outside_cons, outside_nil, and_true]
      have := outside_of_inRanges hw hin
      omega
  · refine h.mf.trans hf fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz⟩ := ho
    refine ⟨hrt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h'
    · omega
    · omega
    · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, -, hin, -⟩
      · omega
      · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hl.readLE a n (h.ext.inRanges_old hin) (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have hsep := h.lsep q (h.ext.mem_old hq)
      simp only [win, outside_cons, outside_nil, and_true] at hsep hz
      rcases (hws r hr).2 with h' | h' | h'
      · omega
      · omega
      · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, -, -, hap⟩
        · omega
        · have := hap q hq; unfold Apart at this; omega

theorem Mid.frame0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) {M2 : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (hws : WsOK s p c ws) (hf : MemFrame M M2 ws) : Mid R b L zp zc xp xl s p c L' b' M2 := by
  have hsp0 := h.sp0
  refine h.frame hws (hf.widen R.rt) (liveFrame_of_memFrame hf) (LiveExt.refl R L') (Nat.le_refl _) ?_
  refine RtInv.inv_frame' hf (fun r hr => ?_) h.inv
  have h0 := (hws r hr).1
  rcases (hws r hr).2 with h' | h' | h'
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact (h.pheld.sub h'.1 (by omega)).symm

theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) (s' : State) (n' : Nat)
    (hm : s'.mem = M) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 3).toNat = n') (h2 : (s'.regs 1).toNat = c)
    (h3 : (s'.regs 7).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat) (hfs : s'.fsBase = s.fsBase)
    (hn : n' ≤ xl.toNat)
    (hv : natVal M p n' = natVal s.mem xp.toNat xl.toNat / y.toNat) (hnorm : NatNorm M p n') :
    PostI R b L zp zc xp xl y s s' := by
  subst hm
  exact ⟨hfs, p, n', c, h0, h1, h2, h3, hv, hnorm, by have := h.cap; omega, hn, L', b', h.ext, h.bud, h.inv,
    fun _ => ⟨h.p8, h.pheld, h.pacc, h.p48⟩, h.ror, h.mf, h.lf⟩

end FvModexp.Amd64.DivW
