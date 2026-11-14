import FvModexp.Proofs.Amd64.Exp.W2Posts
import FvModexp.Proofs.Amd64.Exp.W2OneDefs

set_option autoImplicit false

/-!
# window-2 (amd64): the posts of the cut segments (divmc s79 import-chain cut, second definitions layer)

Definitions hoisted VERBATIM (same namespaces, same names) out of W2Mid/Pre4/Mid2/P01Ret/One/Snc/RR/ORet, after
`W2Posts` and `W2OneDefs`. No statement changes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

/-- the window-2 value from the first window: `outerLoop` over the remaining bits of `y` -/
abbrev zjVal (n Mv k0 : Nat) (tbl : Nat → Nat) (Y ylen yi : Nat) : Nat :=
  Exp.outerLoop 2 (step n Mv k0 tbl) Y 32 (ylen - 1) ((yi * 2 ^ (64 - kTop yi * 2)) % 2 ^ 64) (kTop yi)
    (tbl (yi / 2 ^ (kTop yi * 2)))

/-- what `zj → RET` establishes: the anchor `M0` (frame from `M`), the exit buffers and `TailPost` -/
@[reducible] def ZjPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp yp ylen zp zc zzp zzc : Nat)
    (k0 : Nat) (pp : Nat → Nat) (V : Nat) (st n0 onep bp : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M0 : Memory) (zp' zc' zzp' zzc' : Nat) (Mx : Memory),
    ((zp' = zp ∧ zc' = zc ∧ zzp' = zzp ∧ zzc' = zzc) ∨ (zp' = zzp ∧ zc' = zzc ∧ zzp' = zp ∧ zzc' = zc)) ∧
    MemFrame M M0 (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) ∧ LiveFrame M M0 L [(zp, zp + 8 * n)] ∧
    M0.regions = M.regions ∧
    Bufs R L g fs sp n mp yp ylen pp [(onep, 8 * n), (st, 24)] M0 zp' zc' zzp' zzc' ∧
    Mem R b L g sp M0 Mx zp' zc' zzp' zzc' ∧ Mx.readLE zp' (8 * n) = V ∧
    TailPost R b L g fs sp n mp k0 st n0 bp zp' zc' zzp' zzc' M0 Mx s'

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv)

/-- the memory facts of `zjRet` besides the buffers -/
@[reducible] def Pre4 (R : RtInv) (L : List (Nat × Nat)) (sp n mp mc k0 yp ylen Y yi Mv : Nat) (pp tbl : Nat → Nat)
    (onep st n0 bp r : Nat) (M : Memory) : Prop :=
  Extracted.program.DataLoaded M ∧ Inp R L sp n M mp ∧ Inp R L sp ylen M yp ∧ M.readLE yp (8 * ylen) = Y ∧
  M.readLE (yp + 8 * (ylen - 1)) 8 = yi ∧
  (∀ d, d < 4 → Ent sp n pp (fun _ => 2 * n) tbl M d) ∧ (∀ d, d < 4 → Inp R L sp n M (pp d)) ∧
  M.readLE (sp + 0x280) 8 = ylen ∧ M.readLE (sp + 0x278) 8 = yp ∧ M.readLE (sp + 0x290) 8 = mp ∧
  M.readLE (sp + 0xd8) 8 = k0 ∧ M.readLE (sp + 0x298) 8 = n ∧ M.readLE (sp + 0x2a0) 8 = mc ∧
  NatNorm M mp n ∧ M.readLE mp (8 * n) = Mv ∧
  OneIn R L sp n M onep ∧ M.readLE onep (8 * n) = 1 ∧ M.readLE (sp + 0x210) 8 = onep ∧
  FinEnv sp st n0 bp r M ∧ (InRanges st 24 L ∨ Outside st 24 R.rt)

/-- the frame words the two `make`s may write -/
@[reducible] def LowW (sp : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ q ∈ ws, (sp - 4296 ≤ q.1 ∧ q.2 ≤ sp + 0xd8) ∨ (sp + 0x170 ≤ q.1 ∧ q.2 ≤ sp + 0x178)

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

/-- the old-array facts a reused buffer needs (apart from `m`, `y`, the table, `one`, the stack header) -/
@[reducible] def OldA (n mp yp ylen onep st : Nat) (pp : Nat → Nat) (p c : Nat) : Prop :=
  Apart p (8 * c) mp (8 * n) ∧ Apart p (8 * c) yp (8 * ylen) ∧ (∀ d, d < 4 → Apart p (8 * c) (pp d) (8 * n)) ∧
  Apart p (8 * c) onep (8 * n) ∧ Apart p (8 * c) st 24

/-- the held objects `Bufs` needs the buffers apart from -/
@[reducible] def HeldO (R : RtInv) (L : List (Nat × Nat)) (n mp yp ylen onep st : Nat) (pp : Nat → Nat) : Prop :=
  (InRanges mp (8 * n) L ∨ Outside mp (8 * n) R.rt) ∧ (InRanges yp (8 * ylen) L ∨ Outside yp (8 * ylen) R.rt) ∧
  (∀ d, d < 4 → InRanges (pp d) (8 * n) L ∨ Outside (pp d) (8 * n) R.rt) ∧
  (InRanges onep (8 * n) L ∨ Outside onep (8 * n) R.rt) ∧ (InRanges st 24 L ∨ Outside st 24 R.rt)

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs InpC Inp.c OneIn FinEnv)

/-- `Pre4` without the table and `k0` (the facts at `p01`) -/
@[reducible] def PreT (R : RtInv) (L : List (Nat × Nat)) (sp n mp mc yp ylen Y yi Mv onep st n0 fbp r : Nat)
    (M : Memory) : Prop :=
  Extracted.program.DataLoaded M ∧ Inp R L sp n M mp ∧ Inp R L sp ylen M yp ∧ M.readLE yp (8 * ylen) = Y ∧
  M.readLE (yp + 8 * (ylen - 1)) 8 = yi ∧
  M.readLE (sp + 0x280) 8 = ylen ∧ M.readLE (sp + 0x278) 8 = yp ∧ M.readLE (sp + 0x290) 8 = mp ∧
  M.readLE (sp + 0x298) 8 = n ∧ M.readLE (sp + 0x2a0) 8 = mc ∧
  NatNorm M mp n ∧ M.readLE mp (8 * n) = Mv ∧
  OneIn R L sp n M onep ∧ M.readLE onep (8 * n) = 1 ∧ M.readLE (sp + 0x210) 8 = onep ∧
  FinEnv sp st n0 fbp r M ∧ (InRanges st 24 L ∨ Outside st 24 R.rt)

/-- the old-array facts with the whole table buffer -/
@[reducible] def OldB (n mp yp ylen onep st bp bc : Nat) (p c : Nat) : Prop :=
  Apart p (8 * c) mp (8 * n) ∧ Apart p (8 * c) yp (8 * ylen) ∧ Apart p (8 * c) bp (8 * bc) ∧
  Apart p (8 * c) onep (8 * n) ∧ Apart p (8 * c) st 24

/-- the post of `j4Ret` (from the memory `M` at `j4`) -/
@[reducible] def J4Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp yp ylen zp zc zzp zzc k0 : Nat)
    (pp : Nat → Nat) (V st n0 onep fbp : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (M1 M2 : Memory) (zp1 zc1 zzp2 zzc2 : Nat) (L1 L2 : List (Nat × Nat)) (b1 b2 : Nat),
    ZPost R L L1 b b1 g fs sp n M M1 (zw1 sp) zp zc zp1 zc1 ∧
    ZPost R L1 L2 b1 b2 g fs sp n M1 M2 (zw2 sp) zzp zzc zzp2 zzc2 ∧
    ZjPost R b2 L2 g fs sp n mp yp ylen zp1 zc1 zzp2 zzc2 k0 pp V st n0 onep fbp M2 s'

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

/-- entry of `(*stack).nat` -/
abbrev snE : Nat := 6186112

/-- the slot facts `rrJ → snE` adds (spills and the return address) -/
@[reducible] def OneSl (sp rrp rrl rrc zzp zzc : Nat) (M : Memory) : Prop :=
  M.readLE (sp + 0x220) 8 = rrp ∧ M.readLE (sp + 0x100) 8 = rrc ∧ M.readLE (sp + 0xf8) 8 = rrl ∧
  M.readLE (sp + 0xa0) 8 = zzc ∧ M.readLE (sp + 0x190) 8 = zzp ∧ M.readLE (sp - 8) 8 = p01

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open Janus.Contracts.EqHashModel
open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

/-- the free part of the stack's array -/
@[reducible] def stFree (M : Memory) (st : Nat) : Nat × Nat :=
  (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- a stack-nat call of the window-2 frame: the facts at the call -/
@[reducible] def SnPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp st k : Nat) (M : Memory) : Prop :=
  CallW.CEnv R L g fs (sp - 8) 4288 688 M ∧ RunIface.Serves R ∧ StkOK M R L st ∧
  Apart st 24 (sp - 4296) (4296 + 0x2a8) ∧
  (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4296) (4296 + 0x2a8) ∧
    Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  k ≤ 2 ^ 16 ∧ stLen M st + k + 3 ≤ 2 ^ 16 ∧ stackNatCost (stLen M st) k ≤ b ∧ R.inv b L g (view R.rt L M) ∧
  M.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧ Apart st 24 (stFree M st).1 (stFree M st).2

/-- the callee's post in memory form -/
@[reducible] def SnPost (R : RtInv) (b : Nat) (L L' : List (Nat × Nat)) (b' g sp st k : Nat) (M M' : Memory) : Prop :=
  LiveExt R L L' ∧ b - stackNatCost (stLen M st) k ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧ StkOK M' R L' st ∧
  stLen M' st = stLen M st + StackNat.rnd k ∧
  (stLen M st + StackNat.rnd k ≤ stCap M st → stW M' st = stW M st ∧ stCap M' st = stCap M st) ∧
  (stCap M st < stLen M st + StackNat.rnd k → InRanges (stW M' st) (8 * stCap M' st) R.rt ∧
    ApartAll (stW M' st) (8 * stCap M' st) L) ∧
  MemFrame M M' (R.rt ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st) ∧ LiveFrame M M' L (stkWs M st) ∧
  M'.regions = M.regions ∧
  (stCap M st < stLen M st + StackNat.rnd k → (stW M' st, stW M' st + 8 * stCap M' st) ∈ L')

theorem snE_eq : segAddr Extracted.program StackNat.fn = snE := by decide

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf)

/-- return of `nat.div` (RR) -/
abbrev divRet : Nat := 6212127

/-- the frame words `divRet → rrJ` writes (memmove window + return slot, spills) -/
@[reducible] def rw4 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4104, sp + 0x18), (sp + 0x100, sp + 0x108), (sp + 0x128, sp + 0x130), (sp + 0x248, sp + 0x250)]

/-- the facts at `rrJ` -/
@[reducible] def RRPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n rp rl rc zzp zzc : Nat) (M M' : Memory)
    (rrp rrc : Nat) : Prop :=
  MemFrame M M' (R.rt ++ rw4 sp ++ [(zzp, zzp + 8 * n)]) ∧ LiveFrame M M' L [(zzp, zzp + 8 * n)] ∧
  R.inv b L g (view R.rt L M') ∧ M'.regions = M.regions ∧
  M'.readLE rrp (8 * n) = M.readLE rp (8 * rl) ∧
  ((rrp = rp ∧ rrc = rc ∧ rl = n) ∨ (rrp = zzp ∧ rrc = zzc ∧ rl < n))

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn FinEnv)

/-- `p01Ret`'s conclusion with the operand values given explicitly -/
@[reducible] def RetQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp yp ylen Y yi zp zc zzp zzc t bp bc st n0
    onep fbp Mv xv rv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ Mj : Memory, FP R L sp bp bc M Mj ∧ R.inv b L g (view R.rt L Mj) ∧ Mj.regions = M.regions ∧
    J4Post R b L g fs sp n mp yp ylen zp zc zzp zzc ((2 ^ 64 - t) % 2 ^ 64) (tp bp n)
      (zjVal n Mv ((2 ^ 64 - t) % 2 ^ 64) (Exp.montPow n Mv ((2 ^ 64 - t) % 2 ^ 64) xv rv) Y ylen yi)
      st n0 onep fbp Mj s'

/-- the stack/runtime chain `rrJ → p01` -/
@[reducible] def OneChain (R : RtInv) (b : Nat) (L L2 : List (Nat × Nat)) (b2 sp n st : Nat) (M0 M2 : Memory) : Prop :=
  MemFrame M0 M2 (R.rt ++ (ow sp ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M0 st)) ∧
  LiveFrame M0 M2 L (stkWs M0 st) ∧ LiveExt R L L2 ∧
  b - ((if 4 < n then blockSize (8 * n) true else 0) + stackNatCost (stLen M0 st) (5 * n)) ≤ b2 ∧
  StkOK M2 R L2 st ∧ stLen M2 st = stLen M0 st + StackNat.rnd (5 * n) ∧
  (stLen M0 st + StackNat.rnd (5 * n) ≤ stCap M0 st → stW M2 st = stW M0 st ∧ stCap M2 st = stCap M0 st) ∧
  (stCap M0 st < stLen M0 st + StackNat.rnd (5 * n) → InRanges (stW M2 st) (8 * stCap M2 st) R.rt ∧
    ApartAll (stW M2 st) (8 * stCap M2 st) L) ∧ M2.regions = M0.regions ∧
  (stCap M0 st < stLen M0 st + StackNat.rnd (5 * n) → (stW M2 st, stW M2 st + 8 * stCap M2 st) ∈ L2)

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

theorem apart_held {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart p k a n := by
  rcases hh with h | h
  · exact hap.apart_of_inRanges h
  · have := out_inR h hin; unfold Apart; omega

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

theorem buf_ext {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp n p c : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (hx : LiveExt R L L') (h : Buf R L g fs sp n M p c) (hf : MemFrame M M' ws) : Buf R L' g fs sp n M' p c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨a1, a2, by rw [hf.accessible]; exact a3, a4, hx.held a5, a6, a7, a8⟩

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

theorem buf_frame {R : RtInv} {L : List (Nat × Nat)} {g fs sp n p c : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Buf R L g fs sp n M p c) (hf : MemFrame M M' ws) : Buf R L g fs sp n M' p c := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  exact ⟨a1, a2, by rw [hf.accessible]; exact a3, a4⟩

theorem inp_frame {R : RtInv} {L : List (Nat × Nat)} {sp n p : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Inp R L sp n M p) (hf : MemFrame M M' ws) : Inp R L sp n M' p :=
  ⟨by rw [hf.accessible]; exact h.1, h.2⟩

end FvModexp.Amd64.W2Pro

namespace FvModexp.Amd64.W2Loop


/-- the loop's environment as the callee environment `CEnv` of a call at `RSP = sp - 8` (window = the whole frame) -/
theorem Env.cenv {R : RtInv} {L : List (Nat × Nat)} {g fs sp : Nat} {M0 : Memory} (he : Env R L g fs sp M0)
    (hd : Extracted.program.DataLoaded M0) (hro : RoOut R) : CallW.CEnv R L g fs (sp - 8) 4288 688 M0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := he
  have e1 : sp - 8 - 4288 = sp - 4296 := by omega
  have e2 : sp - 8 + 688 = sp + 0x2a8 := by omega
  unfold CallW.CEnv
  rw [e1, e2]
  exact ⟨by omega, by omega, by omega, h4, h5, h6, by omega, h8, h9, h10, h11, hd, hro, h12.1, h12.2, h13, h14, h16,
    h15⟩

end FvModexp.Amd64.W2Loop
