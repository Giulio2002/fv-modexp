import FvModexp.Proofs.Amd64.Nat.LibBasicMul
import FvModexp.Proofs.Amd64.Nat.AsmCallees
import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.DivmcBits

/-!
# `basicMul(z, x, y nat)` (go-bigmodexpfix natmul.go:151), amd64

```go
func basicMul(z, x, y nat) {
	clear(z[0 : len(x)+len(y)]) // initialize z
	for i, d := range y {
		if d != 0 {
			z[len(x)+i] = addMulVVWW(z[i:i+len(x)], z[i:i+len(x)], x, d, 0)
		}
	}
}
```
See the arm64 twin `FvModexp.Arm64.BasicMul`. Frame `0x70` + saved `RBP`, spills `RAX, RBX, RCX, RDI, RSI, R8, R9, R10`
at `RSP + 8 … RSP + 72` (`above = 72`); calls with `RSP' = RSP - 0x80`: `memclrNoHeapPointers` (`stk = 0x80 + 4096 =
4224`) and `addMulVVWW.abi0` (frame words at `RSP' + 8 …`, result at `RSP' + 96 = RSP - 32`); locals `i` at `RSP - 24`,
`len x + i` at `RSP - 16`. Loop head `+0xcf` (`CMPQ R10, DX`, `DX = i`). Reads `math/big.hasADX` (in `addMulVVWW`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.BasicMul

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.basicMul"
def names : List String := LibBasicMul.names

abbrev head : Nat := segAddr Extracted.program fn + 0xcf

/-- The precondition. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl yp yl : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4224 72 ∧ xl.toNat + yl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat (xl.toNat + yl.toNat) ∧
    Outside zp.toNat (8 * (xl.toNat + yl.toNat)) (win s 4224 72) ∧
    Apart zp.toNat (8 * (xl.toNat + yl.toNat)) ((s.regs 14).toNat + 16) 8 ∧
    Apart zp.toNat (8 * (xl.toNat + yl.toNat)) (s.fsBase.toNat - 8) 8 ∧ s.mem.accessible adxAddr 1 false = true ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4224 72) ∧
    s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
    Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s 4224 72) ∧
    (0 < xl.toNat + yl.toNat → Apart zp.toNat (8 * (xl.toNat + yl.toNat)) xp.toNat (8 * xl.toNat) ∧
      Apart zp.toNat (8 * (xl.toNat + yl.toNat)) yp.toNat (8 * yl.toNat) ∧
      R.ok (cA "runtime.memclrNoHeapPointers") [zp.toNat, 8 * (xl.toNat + yl.toNat)]) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- The postcondition: `z[0 : len x + len y] = x · y`, nothing else written but the stack window and `R.rt`. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp xp xl yp yl : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ natVal s'.mem zp.toNat (xl.toNat + yl.toNat) = natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat yl.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4224 72 ++ [(zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat))]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat))]

/-- What holds at the loop head (iteration `i`, memory `m`): the frame record and the spills, the product so far
`z[0 : len x + i] = x · y[0 : i]`, the rest `z[len x + i : len x + len y]` still zero, `x` and `y` unchanged, the frames
and the runtime invariant. -/
def Inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl : BitVec 64) (s : State) (ret i : Nat)
    (m : Memory) : Prop :=
  m.readLE (s.regs 4).toNat 8 = ret ∧ m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    m.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat ∧
    m.readLE ((s.regs 4).toNat + 8) 8 = zp.toNat ∧ m.readLE ((s.regs 4).toNat + 16) 8 = zl.toNat ∧
    m.readLE ((s.regs 4).toNat + 24) 8 = zc.toNat ∧ m.readLE ((s.regs 4).toNat + 32) 8 = xp.toNat ∧
    m.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat ∧ m.readLE ((s.regs 4).toNat + 48) 8 = xc.toNat ∧
    m.readLE ((s.regs 4).toNat + 56) 8 = yp.toNat ∧ m.readLE ((s.regs 4).toNat + 64) 8 = yl.toNat ∧
    natVal m zp.toNat (xl.toNat + i) = natVal s.mem xp.toNat xl.toNat * natVal s.mem yp.toNat i ∧
    (∀ a k, zp.toNat + 8 * (xl.toNat + i) ≤ a → a + k ≤ zp.toNat + 8 * (xl.toNat + yl.toNat) → m.readLE a k = 0) ∧
    (∀ a k, xp.toNat ≤ a → a + k ≤ xp.toNat + 8 * xl.toNat → m.readLE a k = s.mem.readLE a k) ∧
    (∀ a k, yp.toNat ≤ a → a + k ≤ yp.toNat + 8 * yl.toNat → m.readLE a k = s.mem.readLE a k) ∧
    MemFrame s.mem m (R.rt ++ win s 4224 72 ++ [(zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat))]) ∧
    LiveFrame s.mem m L [(zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat))] ∧
    R.inv b L (s.regs 14).toNat (view R.rt L m)

/-- The facts about the call state the loop steps use (from `Pre`, `0 < len x + len y`). -/
structure Facts (R : RtInv) (L : List (Nat × Nat)) (zp zl xp xl yp yl : BitVec 64) (s : State) : Prop where
  xyz : xl.toNat + yl.toNat ≤ zl.toNat
  sp : 4224 ≤ (s.regs 4).toNat
  zw : zp.toNat + 8 * (xl.toNat + yl.toNat) ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat + 72 ≤ zp.toNat
  xw : xp.toNat + 8 * xl.toNat ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat + 72 ≤ xp.toNat
  yw : yp.toNat + 8 * yl.toNat ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat + 72 ≤ yp.toNat
  zx : Apart zp.toNat (8 * (xl.toNat + yl.toNat)) xp.toNat (8 * xl.toNat)
  zy : Apart zp.toNat (8 * (xl.toNat + yl.toNat)) yp.toNat (8 * yl.toNat)
  zh : Held R L zp.toNat (8 * (xl.toNat + yl.toNat))
  ls : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat + 72 ≤ r.1
  tw : s.fsBase.toNat - 8 + 8 ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat - 4224 + (4224 + 72) ≤ s.fsBase.toNat - 8
  zt : Apart zp.toNat (8 * (xl.toNat + yl.toNat)) (s.fsBase.toNat - 8) 8

/-- A `y` limb `0`: nothing to add. -/
theorem inv_skip {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl : BitVec 64} {s : State}
    {ret i : Nat} {M : Memory} (hI : Inv R b L zp zl zc xp xl xc yp yl s ret i M) (hi : i < yl.toNat)
    (hd : s.mem.readLE (yp.toNat + i * 8) 8 = 0) : Inv R b L zp zl zc xp xl xc yp yl s ret (i + 1) M := by
  obtain ⟨h1, h2, h0, h3, h4, h5, h6, h7, h8, h9, h10, hv, hz, hx, hy, hF, hLF, hinv⟩ := hI
  refine ⟨h1, h2, h0, h3, h4, h5, h6, h7, h8, h9, h10, ?_, fun a k ha hk => hz a k (by omega) hk, hx, hy, hF, hLF, hinv⟩
  rw [show xl.toNat + (i + 1) = xl.toNat + i + 1 by omega, natVal_succ, natVal_succ, hv,
    hz _ _ (by omega) (by omega), show yp.toNat + 8 * i = yp.toNat + i * 8 by omega, hd]
  simp

/-- A nonzero `y` limb `d`: `addMulVVWW(z[i:i+len x], z[i:i+len x], x, d, 0)` (memory `w`, carry `c` at `SP - 32`),
then `z[len x + i] = c`. -/
theorem inv_call {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl : BitVec 64} {s : State}
    {ret i : Nat} {M w : Memory} (hI : Inv R b L zp zl zc xp xl xc yp yl s ret i M) (hi : i < yl.toNat)
    (hf : Facts R L zp zl xp xl yp yl s)
    (hFw : MemFrame M w [((s.regs 4).toNat - 128, (s.regs 4).toNat - 8), (zp.toNat + 8 * i, zp.toNat + 8 * i + 8 * xl.toNat)])
    (hval : natVal w (zp.toNat + 8 * i) xl.toNat + 2 ^ (64 * xl.toNat) * w.readLE ((s.regs 4).toNat - 32) 8 =
      M.readLE (zp.toNat + 8 * i) (8 * xl.toNat) +
        s.mem.readLE xp.toNat (8 * xl.toNat) * s.mem.readLE (yp.toNat + i * 8) 8)
    (hinvw : R.inv b L (s.regs 14).toNat (view R.rt L w)) :
    Inv R b L zp zl zc xp xl xc yp yl s ret (i + 1)
      (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8)) := by
  obtain ⟨h1, h2, h0, h3, h4, h5, h6, h7, h8, h9, h10, hv, hz, hx, hy, hF, hLF, hinv⟩ := hI
  obtain ⟨hxyz, hsp, hzw, hxw, hyw, hzx, hzy, hzh, hls, htw, hzt⟩ := hf
  unfold Apart at hzx hzy hzt
  -- reads outside the stored word and the call's ranges are `M`'s
  have keep : ∀ a k, (a + k ≤ zp.toNat + (xl.toNat + i) * 8 ∨ zp.toNat + (xl.toNat + i) * 8 + 8 ≤ a) →
      Outside a k [((s.regs 4).toNat - 128, (s.regs 4).toNat - 8), (zp.toNat + 8 * i, zp.toNat + 8 * i + 8 * xl.toNat)] →
      (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8)).readLE a k = M.readLE a k := by
    intro a k h1 h2
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hFw.readLE a k h2
  have so : ∀ a, (s.regs 4).toNat - 8 ≤ a → a + 8 ≤ (s.regs 4).toNat + 72 → (a + 8 ≤ (s.regs 4).toNat - 128 ∨ (s.regs 4).toNat - 8 ≤ a) →
      (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8)).readLE a 8 = M.readLE a 8 :=
    fun a ha1 ha2 ha3 => keep a 8 (by omega) (by simp only [Outside, and_true]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [so _ (by omega) (by omega) (by omega)]; exact h1
  · rw [so _ (by omega) (by omega) (by omega)]; exact h2
  · rw [keep _ 8 (by omega) (by simp only [Outside, and_true]; omega)]; exact h0
  · rw [so _ (by omega) (by omega) (by omega)]; exact h3
  · rw [so _ (by omega) (by omega) (by omega)]; exact h4
  · rw [so _ (by omega) (by omega) (by omega)]; exact h5
  · rw [so _ (by omega) (by omega) (by omega)]; exact h6
  · rw [so _ (by omega) (by omega) (by omega)]; exact h7
  · rw [so _ (by omega) (by omega) (by omega)]; exact h8
  · rw [so _ (by omega) (by omega) (by omega)]; exact h9
  · rw [so _ (by omega) (by omega) (by omega)]; exact h10
  · -- the product
    have hlo : natVal (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8)) zp.toNat i =
        natVal M zp.toNat i := keep _ _ (by omega) (by simp only [Outside, and_true]; omega)
    have hmid : natVal (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8))
        (zp.toNat + 8 * i) xl.toNat = natVal w (zp.toNat + 8 * i) xl.toNat :=
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    have htop : (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8)).readLE
        (zp.toNat + 8 * i + 8 * xl.toNat) 8 = w.readLE ((s.regs 4).toNat - 32) 8 := by
      rw [show zp.toNat + 8 * i + 8 * xl.toNat = zp.toNat + (xl.toNat + i) * 8 by omega,
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)]
    have hsM := natVal_add M zp.toNat i xl.toNat
    have hsW := natVal_add (w.writeLE (zp.toNat + (xl.toNat + i) * 8) 8 (w.readLE ((s.regs 4).toNat - 32) 8))
      zp.toNat i (xl.toNat + 1)
    rw [Nat.add_comm i xl.toNat] at hsM
    rw [show i + (xl.toNat + 1) = xl.toNat + (i + 1) by omega, natVal_succ, hmid,
      show zp.toNat + 8 * i + 8 * xl.toNat = zp.toNat + 8 * i + 8 * xl.toNat from rfl, htop, hlo] at hsW
    rw [hsW, natVal_succ, show yp.toNat + 8 * i = yp.toNat + i * 8 by omega]
    rw [hsM] at hv
    exact bm_row _ _ _ _ _ _ _ _ _ hval hv
  · intro a k ha hk
    rw [keep a k (by omega) (by simp only [Outside, and_true]; omega)]
    exact hz a k (by omega) hk
  · intro a k ha hk
    rw [keep a k (by omega) (by simp only [Outside, and_true]; omega)]
    exact hx a k ha hk
  · intro a k ha hk
    rw [keep a k (by omega) (by simp only [Outside, and_true]; omega)]
    exact hy a k ha hk
  · refine MemFrame.writeLE (MemFrame.trans hF hFw ?_) _ (r := (zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat)))
      (by simp) (by simp only; omega) (by simp only; omega)
    intro a n h
    refine ⟨h, ?_⟩
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    omega
  · refine LiveFrame.trans hLF (liveFrame_of_frame (rs := [((s.regs 4).toNat - 128, (s.regs 4).toNat - 8)])
      (lo := (s.regs 4).toNat - 4224) (hi := (s.regs 4).toNat + 72) ?_ hls ?_) (fun _ _ h => h)
    · refine MemFrame.writeLE (hFw.mono fun a n h => ?_) _ (r := (zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat)))
        (by simp) (by simp only; omega) (by simp only; omega)
      simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
      omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only; omega
  · exact inv_store_held hinvw (hzh.sub (by omega) (by omega))

/-- The exit (`i = len y`): the postcondition. -/
theorem post_of_inv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl : BitVec 64} {s s' : State}
    {ret : Nat} (hI : Inv R b L zp zl zc xp xl xc yp yl s ret yl.toNat s'.mem) (hfs : s'.fsBase = s.fsBase) :
    Post R b L zp xp xl yp yl s s' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, hF, hLF, hinv⟩ := hI
  exact ⟨hfs, hv, L, b, LiveExt.refl R L, Nat.le_refl _, hinv, hF, hLF⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem loop (impl : List Amd64.Segment) (R : RtInv) (hMV' : ∀ b L, Summary0 (LibBasicMul.program.link impl)
      (segAddr Extracted.program addMulVVWWfn) (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibBasicMul.program.link impl) ret) (s : State) (hpre : Pre R b L zp zl zc xp xl yp yl s)
    (h0 : 0 < xl.toNat + yl.toNat) (hx15 : s.xmm 15 = 0) :
    ∀ k (S : State) (i : Nat), i + k = yl.toNat → S.rip = BitVec.ofNat 64 head →
      S.regs 0 = zp → S.regs 3 = zl → S.regs 1 = zc → S.regs 7 = xp → S.regs 6 = xl → S.regs 8 = xc →
      S.regs 9 = yp → S.regs 10 = yl → S.regs 2 = BitVec.ofNat 64 i →
      S.regs 4 = s.regs 4 - 120#64 → S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 →
      S.fsBase = s.fsBase →
      Inv R b L zp zl zc xp xl xc yp yl s ret i S.mem →
      Reaches ((LibBasicMul.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp xp xl yp yl s s') := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, ⟨htb, htr, htg⟩, htrt, htw⟩, hxyz, hzc, hz40,
    hzl, hzw, hzg, hzt, hadx, hxacc, hx48, hxh, hxw, hyacc, hy48, hyh, hyw, hap1, hinv0⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hfs : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  obtain ⟨hzx, hzy, -⟩ := hap1 h0
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl h0
  simp only [Outside, and_true] at hzw hxw hyw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat + 72 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, and_true] at this; exact this
  unfold Apart at htw
  have hfacts : Facts R L zp zl xp xl yp yl s := ⟨hxyz, by omega, hzw, hxw, hyw, hzx, hzy, hzh, hLs', htw, hzt⟩
  clear hinv0 hLs
  intro k
  induction k with
  | zero =>
    intro S i hi hpc h0' h1 h2 h3 h4 h5 h6 h7 h8 hsp h14 h5' h15 hfsb hI
    have hI' := hI
    obtain ⟨hr1, hr2, hr0, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hv, hzero, hxs, hys, hF, hLF, hinv⟩ := hI
    janus64_run [hr1, hr2]
    rw [show i = yl.toNat by omega] at hI'
    exact post_of_inv hI' (by first | rfl | exact hfsb | janus64_simp)
  | succ k ih =>
    intro S i hi hpc h0' h1 h2 h3 h4 h5 h6 h7 h8 hsp h14 h5' h15 hfsb hI
    have hI' := hI
    obtain ⟨hr1, hr2, hr0, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hv, hzero, hxs, hys, hF, hLF, hinv⟩ := hI
    have hiy : i < yl.toNat := by omega
    have hi64 : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    have hza1 : s.mem.accessible (zp.toNat + 8 * i) (8 * xl.toNat) true = true :=
      Janus.Arm64.Memory.accessible_mono _ hzacc (by omega) (by omega)
    have hza2 := Janus.Arm64.Memory.accessible_weaken _ hza1
    have hzx1 : zp.toNat + 8 * i = xp.toNat ∨ Apart (zp.toNat + 8 * i) (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
      right; unfold Apart at hzx ⊢; omega
    have hzh1 : InRanges (zp.toNat + 8 * i) (8 * xl.toNat) L ∨ Outside (zp.toNat + 8 * i) (8 * xl.toNat) R.rt :=
      hzh.sub (by omega) (by omega)
    have hzg1 : Apart (zp.toNat + 8 * i) (8 * xl.toNat) ((s.regs 14).toNat + 16) 8 := by unfold Apart at hzg ⊢; omega
    have hzt1 : Apart (zp.toNat + 8 * i) (8 * xl.toNat) (s.fsBase.toNat - 8) 8 := by unfold Apart at hzt ⊢; omega
    have key : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm
    have hmask : ((0#64 - (zc - BitVec.ofNat 64 i)).sshiftRight 63).toNat = 18446744073709551615 := by
      rw [show 0#64 - (zc - BitVec.ofNat 64 i) = BitVec.ofNat 64 i - zc by bv_omega]
      exact sshr63_of_lt _ _ (by omega) (by omega)
    have hand : 18446744073709551615 &&& i * 8 = i * 8 := by rw [Nat.and_comm]; exact and_ones64 _ (by omega)
    have hmod : (zp.toNat + i * 8) % 18446744073709551616 = zp.toNat + 8 * i := by
      rw [mod64_of_lt _ (by omega)]; omega
    janus64_run [hr1, hr2, hr0, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hi64, hfs, hfsb, hmask, hand, hmod] until [head]
      calls [hMV']
    · -- `y[i] = 0`
      refine ih _ (i + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (inv_skip hI' hiy (by janus_assumption))
      all_goals (try janus64_simp)
      all_goals (try exact h15)
    · -- `y[i] ≠ 0`
      rename_i w _ _ hval hFr hinvw hg _
      rw [show (s.regs 4).toNat - 128 + 96 = (s.regs 4).toNat - 32 by omega] at hval
      refine ih _ (i + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (inv_call hI' hiy hfacts (by janus_frame) hval hinvw)
      all_goals (try janus64_simp)
      all_goals (try exact hx15.symm)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zl zc xp xl yp yl) (Post R b L zp xp xl yp yl) := by
  rw [show names = LibBasicMul.names from rfl, ← LibBasicMul.eq_only]
  have hMV := addMulVVWWHyp impl hap
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, ⟨htb, htr, htg⟩, htrt, htw⟩, hxyz, hzc, hz40,
    hzl, hzw, hzg, hzt, hadx, hxacc, hx48, hxh, hxw, hyacc, hy48, hyh, hyw, hap1, hinv⟩ := hpre'
  have hc1 : CodeIn64 ((Extracted.program.onlySegments [addMulVVWWfn]).link impl) (LibBasicMul.program.link impl) := by
    rw [LibBasicMul.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hMV' := fun b L => AddMulVVWWHyp.live (Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc1 hMV) R b L
  have hc2 : CodeIn64 (Extracted.program.ofImpl impl) (LibBasicMul.program.link impl) := by
    rw [LibBasicMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibBasicMul.names
  have hmc' := MemclrNoHeapPointersLive64.of_codeIn hc2 hmc
  clear hc1 hc2 hMV hmc
  janus64_intro hs
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hfs : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  simp only [Outside, and_true] at hzw hxw hyw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4224 ∨ (s.regs 4).toNat + 72 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ win s 4224 72, (s.regs 4).toNat - 4224 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 72 := by
    simp only [win, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  by_cases h0 : xl.toNat + yl.toNat = 0
  · have hx0 : xl.toNat = 0 := by omega
    janus64_run calls [hmc', hMV']
    refine ⟨by first | rfl | janus64_simp, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, by janus_live, ?_, ?_⟩
    · rw [h0]; simp [hx0]
    · simp only [win, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := win s 4224 72) ?_ hLs' hwin
      simp only [win, List.cons_append, List.nil_append]; janus_frame
  obtain ⟨hzx, hzy, hok⟩ := hap1 (by omega)
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hzh2 : InRanges zp.toNat ((xl.toNat + yl.toNat) * 8) L ∨ Outside zp.toNat ((xl.toNat + yl.toNat) * 8) R.rt := by
    rw [Nat.mul_comm]; exact hzh
  have hok' : R.ok (cA "runtime.memclrNoHeapPointers") [zp.toNat, (xl.toNat + yl.toNat) * 8] := by
    rw [Nat.mul_comm]; exact hok
  janus64_run until [head] calls [hmc', hMV']
  rename_i w _ _ hF1 hLF1 hinvw hzeroed
  have hF0 : MemFrame s.mem w (R.rt ++ win s 4224 72 ++ [(zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat))]) := by
    simp only [win, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
  have hLF0 : LiveFrame s.mem w L [(zp.toNat, zp.toNat + 8 * (xl.toNat + yl.toNat))] :=
    LiveFrame.trans (liveFrame_of_frame (rs := win s 4224 72) (by
      simp only [win, List.cons_append, List.nil_append]; janus_frame) hLs' hwin)
      (LiveFrame.mono_ws hLF1 fun a n h => by simp only [Outside, and_true] at h ⊢; omega) (fun _ _ h => h)
  have hz0 := readLE_of_zeroed hzeroed
  unfold Apart at htw
  refine loop impl R hMV' b L zp zl zc xp xl xc yp yl ret hret s hpre (by omega) h_x15 yl.toNat _ 0
    (by omega) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF0, hLF0, hinvw⟩
  -- the frame record, the TLS slot and the spills: through `memclr`'s frame, then the stores
  all_goals try (show Janus.Arm64.Memory.readLE w _ 8 = _; rw [hF1.readLE _ _ (by simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]; refine ⟨⟨?_, by omega, by omega⟩, by unfold Apart at hzt; omega⟩; first | exact htrt | exact Outside.of_sub hout (by omega) (by omega))]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]; first | exact h_ret | exact htg | exact Nat.mod_eq_of_lt (BitVec.isLt _))
  · show natVal w _ _ = _
    simp only [natVal_zero, Nat.mul_zero, Nat.add_zero]
    exact hz0 _ _ (Nat.le_refl _) (by omega)
  · intro a k h1 h2; exact hz0 k a (by omega) (by omega)
  · intro a k h1 h2
    exact Held.readLE2 (hxh.sub h1 h2) hF0 hLF0 (by simp only [win, Outside, and_true]; omega)
      (by simp only [Outside, and_true]; unfold Apart at hzx; omega)
  · intro a k h1 h2
    exact Held.readLE2 (hyh.sub h1 h2) hF0 hLF0 (by simp only [win, Outside, and_true]; omega)
      (by simp only [Outside, and_true]; unfold Apart at hzy; omega)

end FvModexp.Amd64.BasicMul
