import FvModexp.Proofs.Amd64.Nat.LibRsh
import FvModexp.Proofs.Amd64.Nat.NatAddMid
import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Common.DivmcBits

/-!
# `nat.rsh` (go-bigmodexpfix nat.go:425), amd64: statement and segment-boundary facts

The amd64 twin of `FvModexp.Arm64.Rsh` (same Go source; `make`, `set`, `norm`, `same`, `alias` inlined). Arguments
`z = (AX, BX, CX)`, `x = (DI, SI, R8)`, `s = R9`; results `(AX, BX, CX)`. Frame `PUSHQ BP; SUBQ $0x88, SP` (entry
`RSP = e`, `RSP' = e - 0x90`): spills `e + 8, 0x20, 0x28, 0x30`; locals `0x40 = e - 80` (`n`), `0x48 = e - 72` (`c`),
`0x78 = e - 24` (`p`); `rshVU.abi0` frame `0 … 0x30(RSP')`. Callees at `RSP = e - 0x98` with contract stack 4096:
`stk = 4248`, `above = 64`.

The statement is the amd64 twin of asm's arm64 `Rsh.Hyp` (`z` apart from `x`, `x` normalised and non-empty, `s = 0`
only with `cap z = 0`; result `X / 2^s`, need `len x - s/64`), posts with `s'.fsBase = s.fsBase ∧ s'.df = s.df`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)
open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn WrOut NatRes RtPost)

namespace FvModexp.Amd64.Rsh

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh"
def names : List String := LibRsh.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `n = len x - s / 64` (as a natural number; `≤ 0` means the result is empty) -/
@[reducible] def need (xl sh : Nat) : Nat := xl - sh / 64

@[reducible] def RshPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl sh : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ (0 < zc → Apart zp (8 * zc) x (8 * xl)) ∧ NatNorm s.mem x xl ∧ 0 < xl ∧ (0 < sh ∨ zc = 0) ∧
    makeCost (need xl sh) ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

@[reducible] def RshRes (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 3 = BitVec.ofNat 64 l' ∧ s'.regs 1 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (need xl sh) p' l' c' (natVal s.mem x xl / 2 ^ sh) ∧
      (zc < need xl sh → need xl sh ≤ c') ∧
      RtPost R b (makeCost (need xl sh)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- the postcondition (AMD64 DF CONVENTION) -/
@[reducible] def RshPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ RshRes R b L stk above zp zc x xl sh s s'

/-- **The premise shape of `z.rsh(x, s)`** (amd64; `len x ≤ cap x < 2^40` for the `x[m-n:]` slice mask). -/
def Hyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [z, zl, zc, x, xl, xc, sh]
      (fun s => RshPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s ∧
        xl.toNat ≤ xc.toNat ∧ xc.toNat < 2 ^ 40)
      (fun s s' => RshPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl sh : Nat) (s : State) : Prop :=
  RshPre R b L 4248 64 zp zl zc x xl sh s

/-- the postcondition of the internal summaries (DF is in `RegsOK`) -/
@[reducible] def PostI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ RshRes R b L 4248 64 zp zc x xl sh s s'

/-- The registers every path keeps. -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.df = false

/-- The entry state. -/
@[reducible] def Entry (s : State) (zp zl zc x xl xc sh : Nat) : Prop :=
  s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn) ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.xmm 15 = 0#128 ∧ s.df = false ∧ s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧
    s.regs 1 = BitVec.ofNat 64 zc ∧ s.regs 7 = BitVec.ofNat 64 x ∧ s.regs 6 = BitVec.ofNat 64 xl ∧
    s.regs 8 = BitVec.ofNat 64 xc ∧ s.regs 9 = BitVec.ofNat 64 sh

/-- the slice mask `(x - y) >>ₛ 63 & z` with `x < y` (`z[q:]`, `q < cap`) -/
theorem sub_sshr63_and (x y z : BitVec 64) (h : x.toNat < y.toNat) (hy : y.toNat ≤ 2 ^ 63) :
    ((x - y).sshiftRight 63 &&& z) = z := by
  have hm := sshr63_of_lt x y h hy
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hm, Nat.and_comm]
  exact and_ones64 _ z.isLt

theorem shl3 (q : Nat) (h : 8 * q < 2 ^ 64) : BitVec.ofNat 64 q <<< 3 = BitVec.ofNat 64 (8 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem add_c (v k : Nat) (h : v + k < 2 ^ 64) :
    BitVec.ofNat 64 v + BitVec.ofNat 64 k = BitVec.ofNat 64 (v + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem shr6 (sh : Nat) (h : sh < 2 ^ 64) : BitVec.ofNat 64 sh >>> 6 = BitVec.ofNat 64 (sh / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

/-- the entry facts shared by both paths -/
theorem ofNat_ne0 (v : Nat) (h0 : 0 < v) (h : v < 2 ^ 64) : (BitVec.ofNat 64 v = 0#64) = False := by
  simp only [eq_iff_iff, iff_false]; intro e
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega

abbrev hJoinS : Nat := segAddr Extracted.program fn + 0xf2
abbrev hJoin : Nat := segAddr Extracted.program fn + 0x1fe
abbrev callRsh : Nat := segAddr Extracted.program fn + 0x2ac
abbrev hNorm : Nat := segAddr Extracted.program fn + 0x2e0

/-- The segment-boundary facts after the result array `(p, c)` of `z.make(n + 1)` is chosen (`e = RSP` at entry). -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory) : Prop where
  gok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4248 < (s.regs 4).toNat
  tlsg : TlsG s
  trt : Outside (s.fsBase.toNat - 8) 8 R.rt
  tw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 4248) (4248 + 64)
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  g48 : (s.regs 14).toNat + 24 ≤ 2 ^ 48
  al : (s.regs 4).toNat % 8 = 0
  sp0 : 4248 ≤ (s.regs 4).toNat
  sp1 : (s.regs 4).toNat + 64 ≤ 2 ^ 48
  wrt : Outside ((s.regs 4).toNat - 4248) (4248 + 64) R.rt
  gw : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4248) (4248 + 64)
  grt : Outside ((s.regs 14).toNat + 16) 8 R.rt
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  xl16 : xl ≤ 2 ^ 16
  n0 : 0 < need xl sh
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sacc : M.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true
  gacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8
  tacc : M.accessible (s.fsBase.toNat - 8) 8 false = true
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  cap : need xl sh ≤ c
  c40 : c < 2 ^ 40
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) ((s.regs 4).toNat - 4248) (4248 + 64)
  pg : Apart p (8 * c) ((s.regs 14).toNat + 16) 8
  pf : Apart p (8 * c) (s.fsBase.toNat - 8) 8
  pheld : Held R L' p (8 * c)
  px : Apart p (8 * c) x (8 * xl)
  xacc : M.accessible x (8 * xl) false = true
  x48 : x + 8 * xl ≤ 2 ^ 48
  xw : Outside x (8 * xl) (win s 4248 64)
  xr : ∀ a k, x ≤ a → a + k ≤ x + 8 * xl → M.readLE a k = s.mem.readLE a k
  ext : LiveExt R L L'
  bud : b - makeCost (need xl sh) ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4248 64)
  ru : need xl sh ≤ zc → p = zp ∧ c = zc
  ror : (p = zp ∧ c = zc) ∨ (zc < need xl sh ∧ need xl sh ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s 4248 64 ++ [(zp, zp + 8 * zc)])
  lf : LiveFrame s.mem M L [(zp, zp + 8 * zc)]
  sv : Serves R

/-- The ranges written after `Mid`: the window below the saved `RBP`, and the result array. -/
@[reducible] def ws (s : State) (p c : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 4248, (s.regs 4).toNat - 8), (p, p + 8 * c)]

/-- **The postcondition from `Mid`** and the final memory `M'` (`M` changed in `ws`), given the result `(p, l', c)`. -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Janus.Arm64.Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M M' (R.rt ++ ws s p c)) (hLF : LiveFrame M M' L' [(p, p + 8 * c)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M'))
    (s' : State) (l' : Nat) (hm : s'.mem = M') (h0 : s'.regs 0 = BitVec.ofNat 64 p)
    (h1 : s'.regs 3 = BitVec.ofNat 64 l') (h2 : s'.regs 1 = BitVec.ofNat 64 c) (hfs : s'.fsBase = s.fsBase)
    (hl : l' ≤ c) (hv : natVal M' p l' = natVal s.mem x xl / 2 ^ sh) (hn : NatNorm M' p l') :
    PostI R b L zp zc x xl sh s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
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
theorem pre_env {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl sh : Nat} {s : State}
    (hpre : Pre R b L zp zl zc x xl sh s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4248 < (s.regs 4).toNat ∧ 4248 ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + 64 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4248) (4248 + 64) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

end FvModexp.Amd64.Rsh
