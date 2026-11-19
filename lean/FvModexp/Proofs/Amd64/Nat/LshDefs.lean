import FvModexp.Proofs.Amd64.Nat.LibLsh
import FvModexp.Proofs.Amd64.Nat.NatAddMid
import FvModexp.Proofs.Amd64.Exp.EvenHyp
import FvModexp.Proofs.Common.DivmcBits

/-!
# `nat.lsh` (go-bigmodexpfix nat.go:395), amd64: statement and segment-boundary facts

The amd64 twin of `FvModexp.Arm64.Lsh` (same Go source; `make`, `norm`, `same`, `alias` inlined). Arguments
`z = (AX, BX, CX)`, `x = (DI, SI, R8)`, `s = R9`; results `(AX, BX, CX)`.
Frame `PUSHQ BP; SUBQ $0x88, SP` (entry `RSP = e`, return address at `e`, saved `RBP` at `e - 8`, `RSP' = e - 0x90`):
spills `0x98, 0xb0, 0xb8, 0xc0, 0xc8(RSP')` = `e + 8, 0x20, 0x28, 0x30, 0x38` (`above = 64`); locals
`0x68 = e - 40` (`s/64`), `0x60 = e - 48` (`n`), `0x58 = e - 56` (`n + 1`), `0x78 = e - 24` (`p`), `0x40 = e - 80` (`c`),
`lshVU.abi0` frame `0 … 0x30(RSP')`, result `0x38(RSP') = e - 88`. Callees run at `RSP = e - 0x98` with contract stack
4096: `stk = 0x98 + 4096 = 4248`.

The statement (`ens`) is the amd64 twin of infra's `EvenHyp.LshPreA` / expmc's `ExpHyp.LshPost` (window 4248/64,
`z = x` allowed), with the code-forced precondition `0 < s ∧ 0 < len x`, and with the AMD64 DF CONVENTION
(`s'.fsBase = s.fsBase ∧ s'.df = s.df`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)
open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp (RdIn WrOut NatRes RtPost)

namespace FvModexp.Amd64.Lsh

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.lsh"
def names : List String := LibLsh.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `n + 1` with `n = len x + s / 64`: the capacity `z.make(n + 1)` asks for -/
@[reducible] def need (xl sh : Nat) : Nat := xl + sh / 64 + 1

/-- amd64 twin of `Arm64.EvenHyp.LshPreA` (`z = x` allowed) -/
@[reducible] def LshPreA (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl sh : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl + sh / 64 + 1 ≤ 2 ^ 16 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (xl + sh / 64 + 1) ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- the result part of the postcondition (amd64 twin of `Arm64.ExpHyp.LshPost`) -/
@[reducible] def LshRes (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 3 = BitVec.ofNat 64 l' ∧ s'.regs 1 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (xl + sh / 64 + 1) p' l' c' (natVal s.mem x xl * 2 ^ sh) ∧
      (zc < xl + sh / 64 + 1 → xl + sh / 64 + 1 ≤ c') ∧
      RtPost R b (makeCost (xl + sh / 64 + 1)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- the postcondition (AMD64 DF CONVENTION) -/
@[reducible] def LshPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ LshRes R b L stk above zp zc x xl sh s s'

/-- The precondition: `LshPreA` (window `4248 / 64`) and `0 < s ∧ 0 < len x`. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl sh : Nat) (s : State) : Prop :=
  LshPreA R b L 4248 64 zp zl zc x xl sh s ∧ 0 < sh ∧ 0 < xl

/-- the postcondition of the internal summaries (DF is in `RegsOK`) -/
@[reducible] def PostI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ LshRes R b L 4248 64 zp zc x xl sh s s'

/-- The premise shape (amd64 twin of `EvenHyp.LshHypA` with `0 < s ∧ 0 < len x`). -/
def Hyp2 (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [z, zl, zc, x, xl, xc, sh]
      (fun s => LshPreA R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s ∧
        0 < sh.toNat ∧ 0 < xl.toNat)
      (fun s s' => LshPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

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

/-- `z[q:]`'s pointer offset `(q - c) >>ₛ 63 & (q << 3)` with `q < c` -/
theorem sub_shr_mask (q c : Nat) (hq : q < c) (hc : c < 2 ^ 40) :
    ((BitVec.ofNat 64 q - BitVec.ofNat 64 c).sshiftRight 63 &&& BitVec.ofNat 64 q <<< 3) =
      BitVec.ofNat 64 q <<< 3 :=
  sub_sshr63_and _ _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)

/-- the same with `NEGQ` (`0 - (c - q)`) -/
theorem neg_shr_mask (q c : Nat) (hq : q < c) (hc : c < 2 ^ 40) :
    ((0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 q)).sshiftRight 63 &&& BitVec.ofNat 64 q <<< 3) =
      BitVec.ofNat 64 q <<< 3 :=
  neg_sshr63_and _ _ (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem shr6 (sh : Nat) (h : sh < 2 ^ 64) : BitVec.ofNat 64 sh >>> 6 = BitVec.ofNat 64 (sh / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

theorem add_c (v k : Nat) (h : v + k < 2 ^ 64) :
    BitVec.ofNat 64 v + BitVec.ofNat 64 k = BitVec.ofNat 64 (v + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- the entry facts shared by both paths -/
theorem ofNat_ne0 (v : Nat) (h0 : 0 < v) (h : v < 2 ^ 64) : (BitVec.ofNat 64 v = 0#64) = False := by
  simp only [eq_iff_iff, iff_false]; intro e
  have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega

abbrev hJoin : Nat := segAddr Extracted.program fn + 0x1d1
abbrev callLsh : Nat := segAddr Extracted.program fn + 0x28d
abbrev hClr : Nat := segAddr Extracted.program fn + 0x2d2
abbrev hNorm : Nat := segAddr Extracted.program fn + 0x304

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
  n16 : need xl sh ≤ 2 ^ 16
  xl0 : 0 < xl
  sh0 : 0 < sh
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sq : M.readLE ((s.regs 4).toNat - 40) 8 = sh / 64
  sn : M.readLE ((s.regs 4).toNat - 48) 8 = xl + sh / 64
  sn1 : M.readLE ((s.regs 4).toNat - 56) 8 = need xl sh
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
  px : p = x ∨ Apart p (8 * c) x (8 * xl)
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
    (hl : l' ≤ c) (hv : natVal M' p l' = natVal s.mem x xl * 2 ^ sh) (hn : NatNorm M' p l') :
    PostI R b L zp zc x xl sh s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  refine ⟨hfs, p, l', c, h0, h1, h2, L', b', ⟨hv, hn, hl, h.c40, fun _ => ⟨h.p8, h.pheld, ?_, h.p48⟩, h.ru, ?_⟩, ?_,
    ⟨h.ext, h.bud, hinv⟩, ?_, ?_⟩
  · rw [hF.accessible]; exact h.pacc
  · intro hz _
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, hin, hap⟩
    · simp only [need] at hcap; omega
    · exact ⟨hin, hap⟩
  · intro hz
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hkc, -, -⟩
    · simp only [need] at hcap; omega
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
  obtain ⟨⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

end FvModexp.Amd64.Lsh
