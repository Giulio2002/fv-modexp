import FvModexp.Proofs.Amd64.Nat.LibTrunc
import FvModexp.Proofs.Amd64.Nat.NatAddMid
import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Common.DivmcBits

/-!
# `nat.trunc` (go-bigmodexpfix nat.go:530), amd64: statement and segment-boundary facts

The amd64 twin of `FvModexp.Arm64.Trunc` (same Go source; `make`, `set`, `norm` inlined). Arguments
`z = (AX, BX, CX)`, `x = (DI, SI, R8)`, `n = R9`; results `(AX, BX, CX)`.
Frame `PUSHQ BP; SUBQ $0x50, SP` (entry `RSP = e`, return address at `e`, saved `RBP` at `e - 8`, `RSP' = e - 0x58`):
spills `0x60, 0x78, 0x80, 0x90(RSP')` = `e + 8, 0x20, 0x28, 0x38` (`above = 64`); locals `e - 0x40 … e - 0x10`.
Calls `runtime.makeslice` (`make(nat, w, w + 4)` / `make(nat, 1)`) and `runtime.memmove` (`copy`, skipped when the
pointers agree) at `RSP = e - 0x60` with contract stack 4096: `stk = 0x60 + 4096 = 4192`.

The statement is infra's amd64 `EvenHyp.TruncPre`/`TruncPost` (window 4192/64; the post has `fsBase` and `DF`) with
the two code-forced precondition facts of the arm64 proof (`NatNorm x ∨ ⌈n/64⌉ ≤ len x`; `z = x ∨ 0 < cap z ∨
(0 < len x ∧ 0 < n)`, see `FvModexp.Arm64.Trunc`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.Trunc

def fn : String := EvenHyp.fnTrunc
def names : List String := LibTrunc.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `w = ⌈n / 64⌉` -/
@[reducible] def wOf (n : Nat) : Nat := (n + 63) / 64

/-- The precondition: infra's `TruncPre` (window `4192 / 64`) and the two code-forced facts. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl n : Nat) (s : State) : Prop :=
  EvenHyp.TruncPre R b L 4192 64 zp zl zc x xl n s ∧ (NatNorm s.mem x xl ∨ wOf n ≤ xl) ∧
    (zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))

/-- the postcondition of the internal summaries (DF is in `RegsOK`) -/
@[reducible] def PostI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 3 = BitVec.ofNat 64 l' ∧ s'.regs 1 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      EvenHyp.NatRes R L L' s'.mem zp zc (EvenHyp.truncNeed xl n) p' l' c' (natVal s.mem x xl % 2 ^ n) ∧
      (zc < EvenHyp.truncNeed xl n → EvenHyp.truncNeed xl n ≤ c') ∧
      EvenHyp.RtPost R b (makeCost (EvenHyp.truncNeed xl n)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4192 64 ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- The premise shape `EvenHyp.TruncHyp` with the amended precondition. -/
def Hyp2 (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, x, xl, xc, n]
      (fun s => EvenHyp.TruncPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat n.toNat s ∧
        (NatNorm s.mem x.toNat xl.toNat ∨ (n.toNat + 63) / 64 ≤ xl.toNat) ∧
        (z.toNat = x.toNat ∨ 0 < zc.toNat ∨ (0 < xl.toNat ∧ 0 < n.toNat)))
      (fun s s' => EvenHyp.TruncPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat n.toNat s s')

/-- The registers every path keeps. -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.df = false

/-- The entry state. -/
@[reducible] def Entry (s : State) (zp zl zc x xl xc n : Nat) : Prop :=
  s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn) ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧
    s.regs 1 = BitVec.ofNat 64 zc ∧ s.regs 7 = BitVec.ofNat 64 x ∧ s.regs 6 = BitVec.ofNat 64 xl ∧
    s.regs 8 = BitVec.ofNat 64 xc ∧ s.regs 9 = BitVec.ofNat 64 n

theorem shr_w (n : Nat) (hn : n ≤ 2 ^ 20) : (BitVec.ofNat 64 n + 63#64) >>> 6 = BitVec.ofNat 64 (wOf n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  unfold wOf; omega

theorem shr_w' (n : Nat) (hn : n ≤ 2 ^ 20) : (63#64 + BitVec.ofNat 64 n) >>> 6 = BitVec.ofNat 64 (wOf n) := by
  rw [BitVec.add_comm]; exact shr_w n hn

theorem ofNat_ne0 (v : Nat) (h0 : 0 < v) (h : v < 2 ^ 64) : (BitVec.ofNat 64 v = 0#64) = False := by
  simp only [eq_iff_iff, iff_false]; intro e
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega

abbrev hJoin : Nat := segAddr Extracted.program fn + 0xbb
abbrev hTst : Nat := segAddr Extracted.program fn + 0x100
abbrev hJoinS : Nat := segAddr Extracted.program fn + 0x1a2
abbrev hNorm : Nat := segAddr Extracted.program fn + 0x1e7

/-- The segment-boundary facts after the result array `(p, c)` of `z.make(k)` is chosen (`0 < c`; `e = RSP`). -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat) (s : State)
    (k p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory) : Prop where
  gok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4192 < (s.regs 4).toNat
  tlsg : TlsG s
  trt : Outside (s.fsBase.toNat - 8) 8 R.rt
  tw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 4192) (4192 + 64)
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  g48 : (s.regs 14).toNat + 24 ≤ 2 ^ 48
  al : (s.regs 4).toNat % 8 = 0
  sp0 : 4192 ≤ (s.regs 4).toNat
  sp1 : (s.regs 4).toNat + 64 ≤ 2 ^ 48
  wrt : Outside ((s.regs 4).toNat - 4192) (4192 + 64) R.rt
  gw : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4192) (4192 + 64)
  grt : Outside ((s.regs 14).toNat + 16) 8 R.rt
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  xl16 : xl ≤ 2 ^ 16
  kx : k ≤ xl
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sn : k = wOf n → M.readLE ((s.regs 4).toNat + 0x38) 8 = n
  sacc : M.accessible ((s.regs 4).toNat - 4192) (4192 + 64) true = true
  gacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8
  tacc : M.accessible (s.fsBase.toNat - 8) 8 false = true
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  c0 : 0 < c
  cap : k ≤ c
  c40 : c < 2 ^ 40
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) ((s.regs 4).toNat - 4192) (4192 + 64)
  pg : Apart p (8 * c) ((s.regs 14).toNat + 16) 8
  pf : Apart p (8 * c) (s.fsBase.toNat - 8) 8
  pheld : Held R L' p (8 * c)
  px : 0 < k → p = x ∨ Apart p (8 * c) x (8 * xl)
  xacc : M.accessible x (8 * xl) false = true
  x48 : x + 8 * xl ≤ 2 ^ 48
  xw : Outside x (8 * xl) (win s 4192 64)
  xr : ∀ a k, x ≤ a → a + k ≤ x + 8 * xl → M.readLE a k = s.mem.readLE a k
  ext : LiveExt R L L'
  bud : b - makeCost k ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4192 64)
  ru : k ≤ zc → p = zp ∧ c = zc
  ror : (p = zp ∧ c = zc) ∨ (zc < k ∧ k ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s 4192 64 ++ [(zp, zp + 8 * zc)])
  lf : LiveFrame s.mem M L [(zp, zp + 8 * zc)]
  sv : Serves R

/-- The ranges written after `Mid`: the window below the saved `RBP`, and the result array. -/
@[reducible] def ws (s : State) (p c : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 4192, (s.regs 4).toNat - 8), (p, p + 8 * c)]

/-- **The postcondition from `Mid`** and the final memory `M'` (`M` changed in `ws`), given the result `(p, l', c)`. -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl n : Nat} {s : State}
    {k p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Janus.Arm64.Memory}
    (h : Mid R b L zp zc x xl n s k p c L' b' M) (hk : k = EvenHyp.truncNeed xl n)
    (hF : MemFrame M M' (R.rt ++ ws s p c)) (hLF : LiveFrame M M' L' [(p, p + 8 * c)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M'))
    (s' : State) (l' : Nat) (hm : s'.mem = M') (h0 : s'.regs 0 = BitVec.ofNat 64 p)
    (h1 : s'.regs 3 = BitVec.ofNat 64 l') (h2 : s'.regs 1 = BitVec.ofNat 64 c) (hfs : s'.fsBase = s.fsBase)
    (hl : l' ≤ c) (hv : natVal M' p l' = natVal s.mem x xl % 2 ^ n) (hn : NatNorm M' p l') :
    PostI R b L zp zc x xl n s s' := by
  subst hm hk
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap; have hc0 := h.c0
  unfold Apart at hpw
  refine ⟨hfs, p, l', c, h0, h1, h2, L', b', ⟨hv, hn, hl, h.c40, fun _ => ⟨h.p8, h.pheld, ?_, h.p48⟩, h.ru, ?_⟩, ?_,
    ⟨h.ext, h.bud, hinv⟩, ?_, ?_⟩
  · rw [hF.accessible]; exact h.pacc
  · intro hz _
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, hin, hap⟩
    · omega
    · exact ⟨hin, hap⟩
  · intro hz
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hkc, -, -⟩
    · omega
    · exact hkc
  · refine h.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, ws, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz⟩ := ho
    refine ⟨hrt, by omega, ?_⟩
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, hin, -⟩
    · omega
    · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n (h.ext.inRanges_old hin) ?_]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      simp only [outside_cons, outside_nil, and_true] at hz ⊢
      rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, -, hap⟩
      · omega
      · have := hap q hq; unfold Apart at this; omega

/-- The facts of the entry state every constructor needs (amd64 `CallEnv` destructured). -/
theorem pre_env {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n : Nat} {s : State}
    (hpre : Pre R b L zp zl zc x xl n s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4192 < (s.regs 4).toNat ∧ 4192 ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + 64 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4192) (4192 + 64) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

end FvModexp.Amd64.Trunc
