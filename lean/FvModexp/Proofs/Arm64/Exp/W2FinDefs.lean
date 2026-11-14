import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Defs
import FvModexp.Proofs.Arm64.Exp.W2ZcDefs
import FvModexp.Proofs.Arm64.Exp.DeferW
import FvModexp.Proofs.Common.ExpNorm

/-!
# window-2 (arm64): the posts of the function's tail (definitions only)

Hoisted (s67) out of `W2Fin`, `W2ExitS`, `W2Tail` and `W2Mid` (unchanged text, same namespaces) so that the
segments of window-2 that only STATE these posts do not import the modules that prove them (row import-chain cut).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.DeferW

/-- the `stk.restore` closure of window-2 -/
def fnW2 : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1"

end FvModexp.Arm64.DeferW

namespace FvModexp.Arm64.W2Loop

/-- what the end guarantees (memory relative to the memory `M` at the join point) -/
@[reducible] def FinPost (sp g st n0 p l c : Nat) (r18 r29 : BitVec 64) (M : Memory) (s' : State) : Prop :=
  s'.sp = BitVec.ofNat 64 (sp + 640) ∧ s'.regs 18 = r18 ∧ s'.regs 28 = BitVec.ofNat 64 g ∧ s'.regs 29 = r29 ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧
    MemFrame M s'.mem [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)]

/-- the static facts of the end -/
@[reducible] def FinEnv (sp g st n0 : Nat) (r29 : BitVec 64) (ret : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ 4288 ≤ sp ∧ sp + 752 ≤ 2 ^ 48 ∧ M.accessible (sp - 4288) (4288 + 752) true = true ∧
    g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + 4288 < sp ∧
    Apart (g + 16) 8 (sp - 4288) (4288 + 752) ∧
    M.readLE (sp + 624) 8 = sp + 552 ∧ M.readLE (sp + 552) 8 = segAddr LibW.program DeferW.fnW2 ∧
    M.readLE (sp + 560) 8 = st ∧ M.readLE (sp + 568) 8 = n0 ∧
    (st + 24 ≤ 2 ^ 48 ∧ st ≠ 0) ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 4288) (4288 + 752) ∧ Apart st 24 (g + 16) 8 ∧
    M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret

/-- the written ranges from the first `zz.cmp(m)` to the join: callee windows, spills, `zz`'s array -/
@[reducible] def jw (R : RtInv) (sp zzp zzc : Nat) : List (Nat × Nat) :=
  R.rt ++ [(sp - 4304, sp - 8), (sp + 8, sp + 80), (sp + 160, sp + 176), (sp + 400, sp + 408)] ++ [(zzp, zzp + 8 * zzc)]

/-- what holds at the join point `njoin` (memory `M'`, result `(p, l, c)` in `X3..X5`) relative to the memory `M`
before the final reduction -/
@[reducible] def JoinPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n zzp zzc V : Nat) (M : Memory)
    (p l c : Nat) (M' : Memory) : Prop :=
  ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost n ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧
    M'.regions = M.regions ∧ MemFrame M M' (jw R sp zzp zzc) ∧ LiveFrame M M' L [(zzp, zzp + 8 * zzc)] ∧
    natVal M' p l = V ∧ l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧ NatLive M' R L' p c ∧
    ((p = zzp ∧ c = zzc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
    (l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M'.accessible p (8 * l) false = true))

/-- what the return state satisfies, from the loop exit (memory `M`) -/
@[reducible] def TailPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp k0 st n0 zp zc zzp zzc : Nat)
    (r18 r29 : BitVec 64) (M0 M : Memory) (s' : State) : Prop :=
  ∃ (M' Mj : Memory) (p l c : Nat), Mem R b L g sp M0 M' zp zc zzp zzc ∧
    M'.readLE zzp (8 * n) = Exp.montgomery n (M.readLE zp (8 * n)) 1 (M0.readLE mp (8 * n)) k0 ∧
    JoinPost R b L g sp n zzp zzc
      (if M0.readLE mp (8 * n) ≤ M'.readLE zzp (8 * n) then 0 else M'.readLE zzp (8 * n)) M' p l c Mj ∧
    FinPost sp g st n0 p (Expmc.normL Mj p l) c r18 r29 Mj s'

theorem FinEnv.stnz {sp g st n0 : Nat} {r29 : BitVec 64} {ret : Nat} {M : Memory} (h : FinEnv sp g st n0 r29 ret M) :
    st ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨-, h⟩, -⟩ := h
  exact h

end FvModexp.Arm64.W2Loop

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf Bufs Mem FinEnv TailPost step)

theorem reaches_mono {p : Program} {s : State} {Q Q' : Outcome → Prop} (h : Reaches p s Q) (hq : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h1, h2⟩ := h
  exact ⟨n, o, h1, hq o h2⟩

theorem isReturn_mono {P P' : State → Prop} (hq : ∀ s, P s → P' s) : ∀ o, IsReturn P o → IsReturn P' o := by
  intro o h
  cases o <;> simp only [IsReturn] at h ⊢
  all_goals first | exact hq _ h | exact h

/-- the window-2 value from the first window: `outerLoop` over the remaining bits of `y` -/
abbrev zjVal (n Mv k0 : Nat) (tbl : Nat → Nat) (Y ylen yi : Nat) : Nat :=
  Exp.outerLoop 2 (step n Mv k0 tbl) Y 32 (ylen - 1) ((yi * 2 ^ (64 - kTop yi * 2)) % 2 ^ 64) (kTop yi)
    (tbl (yi / 2 ^ (kTop yi * 2)))

/-- what `zj → RET` establishes: the anchor `M0` (frame from `M`), the exit buffers and `TailPost` -/
@[reducible] def ZjPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen bp zp zc zzp zzc : Nat)
    (tbl : Nat → Nat) (V : Nat) (st n0 onep : Nat) (r18 r29 : BitVec 64) (M : Memory) (s' : State) : Prop :=
  ∃ (M0 : Memory) (zp' zc' zzp' zzc' : Nat) (Mx : Memory),
    ((zp' = zp ∧ zc' = zc ∧ zzp' = zzp ∧ zzc' = zzc) ∨ (zp' = zzp ∧ zc' = zzc ∧ zzp' = zp ∧ zzc' = zc)) ∧
    MemFrame M M0 (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) ∧ LiveFrame M M0 L [(zp, zp + 8 * n)] ∧
    M0.regions = M.regions ∧
    Bufs R L g sp n mp yp ylen (fun d => bp + 8 * (d * n)) [(onep, 8 * n), (st, 24)] M0 zp' zc' zzp' zzc' ∧
    Mem R b L g sp M0 Mx zp' zc' zzp' zzc' ∧ Mx.readLE zp' (8 * n) = V ∧
    TailPost R b L g sp n mp k0 st n0 zp' zc' zzp' zzc' r18 r29 M0 Mx s'

theorem buf_frame {R : RtInv} {L : List (Nat × Nat)} {g sp n p c : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Buf R L g sp n M p c) (hf : MemFrame M M' ws) : Buf R L g sp n M' p c := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  exact ⟨a1, a2, by rw [hf.accessible]; exact a3, a4⟩

end FvModexp.Arm64.W2Pro
