import FvModexp.Proofs.Arm64.Exp.W4En
import FvModexp.Proofs.Arm64.Exp.W4FunO
import FvModexp.Proofs.Arm64.Exp.W4FunV

/-!
# `nat.expNNOddMontgomeryWindowSize4` (arm64): the function-level summary (CONVENTIONS §3)

`ens`: from the entry facts `W4En.EPre` (+ `m` odd, `1 < m`, a stack-length bound and a closed budget) the call
returns `x^y mod m` in `X0..X2` (normalised; the result array is `z`'s or a fresh runtime object), with the live set
extended, the budget reduced by at most `W4Cost`, the stack back at its entry length (array kept or fresh), and memory
changed only in `R.rt`, the frame window (not the caller's saved FP/LR), `z`'s array and the stack's header and free
part. Composed from `W4En.enStep` (entry → `RET`) and the posts of the chain (`EnPost`, `XnPost`, `DivRetPost`, …).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpW4

open FvModexp.Arm64.W4Pro (xjBud xnBudA xnBudAC xnPre Zw rd_step ap_fresh arr_ap akf_trans out_S0 out_S1 out_S2 out_S3 out_S4 out_S5 out_S6 out_S7 out_S8 out_S9 apartAll_ext)
open FvModexp.Arm64.W4En (EPre EnPost)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4"

/-- the names of the program window-4 is proved on (`LibExp.names`: every function of the exp layer) -/
abbrev names : List String := LibExp.names

/-- the closed budget the precondition asks for (`l` = the stack length at entry, `k = len x - n + 1`) -/
def W4Bud (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + (xjBud n costD (l + StackNat.rnd (23 * n)) +
    (stackNatCost (l + StackNat.rnd (23 * n)) n + xjBud n costD (l + StackNat.rnd (23 * n) + StackNat.rnd n)) +
    xnBudA n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) + xnBudAC n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) +
    xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1))

/-- the cost the postcondition charges -/
def W4Cost (n xl costD l : Nat) : Nat :=
  stackNatCost l (23 * n) + xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) + blockSize (8 * n) true +
    stackNatCost (2 ^ 16) (17 * n) + blockSize (8 * (2 * n + 4)) true + makeCost n

/-- the precondition: the entry facts (frame `sp = SP - 928`, window `[sp - K, sp + 1040)`), `m` odd and `> 1`, the
stack-length bound, the budget -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (zp zc st xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EPre R b L K (s.regs 28).toNat (s.sp.toNat - 928) st zp zc xp xl xc yp ylen mp n mc s ∧
  natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧
  stLen s.mem st + StackNat.rnd (23 * n) + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 4 * xl + StackNat.rnd n +
    2 * StackNat.rnd (2 * n) + 17 * n + 68 ≤ 2 ^ 16 ∧
  W4Bud n xl costD (stLen s.mem st) ≤ b

/-- the postcondition (results `X0..X2`) -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD : Nat) (zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ c < 2 ^ 64 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - W4Cost n xl costD (stLen s.mem st) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBack R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s (K + 928) 112 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st)

theorem buds {n xl costD l b : Nat} (h : W4Bud n xl costD l ≤ b) :
    stackNatCost l (23 * n) + xjBud n costD (l + StackNat.rnd (23 * n)) ≤ b ∧
    stackNatCost l (23 * n) + (stackNatCost (l + StackNat.rnd (23 * n)) n +
      xjBud n costD (l + StackNat.rnd (23 * n) + StackNat.rnd n)) ≤ b ∧
    stackNatCost l (23 * n) + xnBudA n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b ∧
    stackNatCost l (23 * n) + xnBudAC n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b ∧
    stackNatCost l (23 * n) + xnPre n costD (l + StackNat.rnd (23 * n)) (xl - n + 1) ≤ b := by
  unfold W4Bud at h; omega

theorem bud_fin {b b1 bd b2 b' b'' s0 P bs8 iff17 snc17 bsz mk n : Nat} (hb1 : b - s0 ≤ b1) (hbd : b1 - P ≤ bd)
    (hb3 : bd - (iff17 + snc17) ≤ b2) (hb5 : b2 - bsz ≤ b') (hb8 : b' - mk ≤ b'') (hif : iff17 ≤ bs8)
    (hs : snc17 ≤ stackNatCost (2 ^ 16) (17 * n)) :
    b - (s0 + P + bs8 + stackNatCost (2 ^ 16) (17 * n) + bsz + mk) ≤ b'' := by omega

theorem snc_mono {l n : Nat} (h : l ≤ 2 ^ 16) : stackNatCost l n ≤ stackNatCost (2 ^ 16) n := by
  unfold stackNatCost allocCost; omega

theorem if_le (n : Nat) : (if 4 < n then blockSize (8 * n) true else 0) ≤ blockSize (8 * n) true := by
  split <;> omega


theorem bp_ap {a k W l c n : Nat} (h : a + k ≤ W + 8 * l ∨ W + 8 * c ≤ a) (hc : l + 17 * n ≤ c) :
    a + k ≤ W + 8 * l ∨ W + 8 * l + 8 * (17 * n) ≤ a := by omega

theorem lc_of {l c c' rl n : Nat} (h1 : c' = l + rl) (h2 : 17 * n ≤ rl) (h3 : c' ≤ c) : l + 17 * n ≤ c := by omega

theorem out9_0 {sp K st : Nat} (hw : Zw sp K st 8) (hK : 4304 ≤ K) :
    Outside st 8 [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
  simp only [Zw, outside_cons, outside_nil, and_true] at hw ⊢; omega

theorem out9_16 {sp K st : Nat} (hw : Zw sp K (st + 16) 8) (hK : 4304 ≤ K) :
    Outside (st + 16) 8 [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
  simp only [Zw, outside_cons, outside_nil, and_true] at hw ⊢; omega

theorem zw_sub {sp K a k b q : Nat} (h : Apart a k (sp - K) (K + 1040)) (h1 : a ≤ b) (h2 : b + q ≤ a + k)
    (hK : K ≤ sp) : Zw sp K b q := by
  unfold Apart at h; simp only [Zw]; omega

theorem ap_sub {a k b q x y : Nat} (h : Apart a k x y) (h1 : a ≤ b) (h2 : b + q ≤ a + k) : b + q ≤ x ∨ x + y ≤ b := by
  unfold Apart at h; omega

theorem ap_of {a k x y : Nat} (h : Apart a k x y) : a + k ≤ x ∨ x + y ≤ a := h

theorem ap_of' {a k x y : Nat} (h : Apart x y a k) : a + k ≤ x ∨ x + y ≤ a := by unfold Apart at h; omega

theorem free_ap {a k W l c : Nat} (h : Apart a k (W + 8 * l) (8 * (c - l))) (hl : l ≤ c) :
    a + k ≤ W + 8 * l ∨ W + 8 * c ≤ a := by unfold Apart at h; omega

theorem n_le_of {n z : Nat} (h : 2 * n + 1 ≤ z) : n ≤ z := by omega
theorem n_le_of2 {n z : Nat} (h : 2 * n ≤ z) : n ≤ z := by omega

theorem hdr_zw {sp K st : Nat} (h : Apart st 24 (sp - K) (K + 1040)) (hK : K ≤ sp) : Zw sp K st 24 := by
  unfold Apart at h; simp only [Zw]; omega

/-- the header's 8-byte fields from a read of the whole header -/
theorem hdr_fields {M M' : Memory} {st : Nat} (h : M'.readLE st 24 = M.readLE st 24) :
    stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st :=
  ⟨W4Pro.readLE_sub_eq h (Nat.le_refl _) (by omega), W4Pro.readLE_sub_eq h (by omega) (by omega),
    W4Pro.readLE_sub_eq h (by omega) (by omega)⟩

theorem out9_hdr {sp K st : Nat} (hw : Zw sp K st 24) (hK : 4304 ≤ K) :
    Outside st 8 [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] ∧
    Outside (st + 16) 8 [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
  simp only [Zw, outside_cons, outside_nil, and_true] at hw ⊢; omega

/-- the old-or-fresh `z'` of `z.make(2n)` misses a held range outside `z` -/
theorem z'_ap {R : RtInv} {L L2 : List (Nat × Nat)} {zp zc zp' zc' n a k : Nat}
    (hzo : (zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L2)) (hx : LiveExt R L L2)
    (hh : Outside a k R.rt ∨ InRanges a k L) (h2n : 2 * n ≤ zc') (hz : 2 * n ≤ zc → a + k ≤ zp ∨ zp + 8 * zc ≤ a) :
    a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a := by
  rcases hzo with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · exact hz h2n
  · exact ap_fresh hin hap hx hh

/-- the loop's buffers are `z'` and `zz` (in some order) -/
theorem bufs_ap {zp' zc' zzp zzc zp'' zc'' zzp'' zzc'' a k : Nat}
    (hP : (zp'' = zp' ∧ zc'' = zc' ∧ zzp'' = zzp ∧ zzc'' = zzc) ∨ (zp'' = zzp ∧ zc'' = zzc ∧ zzp'' = zp' ∧ zzc'' = zc'))
    (h1 : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a) (h2 : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    (a + k ≤ zp'' ∨ zp'' + 8 * zc'' ≤ a) ∧ (a + k ≤ zzp'' ∨ zzp'' + 8 * zzc'' ≤ a) := by
  rcases hP with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

/-- the segment chain from the entry memory to the return memory: a held range outside window-4's frame, the stack's
header, the entry free part and (when reused) `z` reads the same at the return (and at the loop anchor `M0z`) -/
theorem chainA {R : RtInv} {L L1 Ld L2 L' : List (Nat × Nat)} {sp K st n zzp zzc zp' zc' zp'' zc'' zzp'' zzc''
    lenM : Nat} {M0 M Md M1 M2 Mj M' M0z M'' Mj2 Me : Memory}
    (hK : 4304 ≤ K)
    (hF0 : MemFrame M0 M (R.rt ++ [(sp - K, sp + 920), (sp + 936, sp + 1040), (st, st + 24)]))
    (hLF0 : LiveFrame M0 M L [(st, st + 24)])
    (hx0 : LiveExt R L L1) (hFd : MemFrame M Md (R.rt ++ W4Pro.aw sp K st M))
    (hLFd : LiveFrame M Md L1 [(st, st + 24), W4Pro.frA st M]) (hxd : LiveExt R L Ld)
    (hF2 : MemFrame Md M1 (R.rt ++ W4Pro.rw4 sp ++ [(zzp, zzp + 8 * n)])) (hLF2 : LiveFrame Md M1 Ld [(zzp, zzp + 8 * n)])
    (hF3 : MemFrame M1 M2 (R.rt ++ W4Pro.ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M1 st))
    (hLF3 : LiveFrame M1 M2 Ld (stkWs M1 st)) (hx2 : LiveExt R L L2)
    (hF4 : MemFrame M2 Mj (R.rt ++ W4Pro.tw sp (stW M2 st + 8 * lenM) n))
    (hLF4 : LiveFrame M2 Mj L2 [(stW M2 st + 8 * lenM, stW M2 st + 8 * lenM + 8 * (17 * n))])
    (hF5 : MemFrame Mj M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 152)])) (hLF5 : LiveFrame Mj M' L2 [])
    (hx5 : LiveExt R L L')
    (hF6 : MemFrame M' M0z (R.rt ++ W4Pro.cw sp ++ [(zp', zp' + 8 * n)])) (hLF6 : LiveFrame M' M0z L' [(zp', zp' + 8 * n)])
    (hF7 : MemFrame M0z M'' (W4Loop.lw R sp zp'' zc'' zzp'' zzc''))
    (hLF7 : LiveFrame M0z M'' L' [(zp'', zp'' + 8 * zc''), (zzp'', zzp'' + 8 * zzc'')])
    (hF8 : MemFrame M'' Mj2 (W4Loop.jw R sp zzp'' zzc'')) (hLF8 : LiveFrame M'' Mj2 L' [(zzp'', zzp'' + 8 * zzc'')])
    (hF9 : MemFrame Mj2 Me [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)])
    {a k : Nat} (hh : Outside a k R.rt ∨ InRanges a k L) (hw : Zw sp K a k) (hd : a + k ≤ st ∨ st + 24 ≤ a)
    (hM : a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) (hlcM : stLen M st ≤ stCap M st)
    (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) (hnz : n ≤ zzc)
    (hM1 : a + k ≤ stW M1 st + 8 * stLen M1 st ∨ stW M1 st + 8 * stCap M1 st ≤ a)
    (hbp : a + k ≤ stW M2 st + 8 * lenM ∨ stW M2 st + 8 * lenM + 8 * (17 * n) ≤ a)
    (hz' : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a) (hnz' : n ≤ zc')
    (hz'' : a + k ≤ zp'' ∨ zp'' + 8 * zc'' ≤ a) (hzz'' : a + k ≤ zzp'' ∨ zzp'' + 8 * zzc'' ≤ a) :
    M0z.readLE a k = M0.readLE a k ∧ Me.readLE a k = M0.readLE a k := by
  simp only [List.append_assoc] at hF2 hF3 hF6
  simp only [W4Loop.lw, W4Loop.jw, List.append_assoc] at hF7 hF8
  have e0 := rd_step hF0 hLF0 (LiveExt.refl R L) hh (out_S0 hw hd).1 (out_S0 hw hd).2
  have e1 := rd_step hFd hLFd hx0 hh (out_S1 hw hd hM hlcM).1 (out_S1 hw hd hM hlcM).2
  have e2 := rd_step hF2 hLF2 hxd hh (out_S2 hw hK hzz hnz).1 (out_S2 hw hK hzz hnz).2
  have e3 := rd_step hF3 hLF3 hxd hh (out_S3 hw hK hd hM1).1 (out_S3 hw hK hd hM1).2
  have e4 := rd_step hF4 hLF4 hx2 hh (out_S4 hw hK hbp).1 (out_S4 hw hK hbp).2
  have e5 := rd_step hF5 hLF5 hx2 hh (out_S5 hw hK) trivial
  have e6 := rd_step hF6 hLF6 hx5 hh (out_S6 hw hK hz' hnz').1 (out_S6 hw hK hz' hnz').2
  have e7 := rd_step hF7 hLF7 hx5 hh (out_S7 hw hK hz'' hzz'').1 (out_S7 hw hK hz'' hzz'').2
  have e8 := rd_step hF8 hLF8 hx5 hh (out_S8 hw hK hzz'').1 (out_S8 hw hK hzz'').2
  have e9 := hF9.readLE a k (out_S9 hw hK hd)
  have h6 : M0z.readLE a k = M0.readLE a k := by rw [e6, e5, e4, e3, e2, e1, e0]
  exact ⟨h6, by rw [e9, e8, e7, h6]⟩

/-- the stack header (written only by the `stk.nat(17n)` call and the final `stk.restore`) through the other
segments -/
theorem chainH {R : RtInv} {L Ld L2 L' : List (Nat × Nat)} {sp K n zzp zzc zp' zc' zp'' zc'' zzp'' zzc''
    lenM : Nat} {Md M1 M2 Mj M' M0z M'' Mj2 : Memory} {st : Nat}
    (hK : 4304 ≤ K) (hxd : LiveExt R L Ld)
    (hF2 : MemFrame Md M1 (R.rt ++ W4Pro.rw4 sp ++ [(zzp, zzp + 8 * n)])) (hLF2 : LiveFrame Md M1 Ld [(zzp, zzp + 8 * n)])
    (hx2 : LiveExt R L L2)
    (hF4 : MemFrame M2 Mj (R.rt ++ W4Pro.tw sp (stW M2 st + 8 * lenM) n))
    (hLF4 : LiveFrame M2 Mj L2 [(stW M2 st + 8 * lenM, stW M2 st + 8 * lenM + 8 * (17 * n))])
    (hF5 : MemFrame Mj M' (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 152)])) (hLF5 : LiveFrame Mj M' L2 [])
    (hx5 : LiveExt R L L')
    (hF6 : MemFrame M' M0z (R.rt ++ W4Pro.cw sp ++ [(zp', zp' + 8 * n)])) (hLF6 : LiveFrame M' M0z L' [(zp', zp' + 8 * n)])
    (hF7 : MemFrame M0z M'' (W4Loop.lw R sp zp'' zc'' zzp'' zzc''))
    (hLF7 : LiveFrame M0z M'' L' [(zp'', zp'' + 8 * zc''), (zzp'', zzp'' + 8 * zzc'')])
    (hF8 : MemFrame M'' Mj2 (W4Loop.jw R sp zzp'' zzc'')) (hLF8 : LiveFrame M'' Mj2 L' [(zzp'', zzp'' + 8 * zzc'')])
    {a k : Nat} (hh : Outside a k R.rt ∨ InRanges a k L) (hw : Zw sp K a k)
    (hzz : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) (hnz : n ≤ zzc)
    (hbp : a + k ≤ stW M2 st + 8 * lenM ∨ stW M2 st + 8 * lenM + 8 * (17 * n) ≤ a)
    (hz' : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a) (hnz' : n ≤ zc')
    (hz'' : a + k ≤ zp'' ∨ zp'' + 8 * zc'' ≤ a) (hzz'' : a + k ≤ zzp'' ∨ zzp'' + 8 * zzc'' ≤ a) :
    M1.readLE a k = Md.readLE a k ∧ Mj2.readLE a k = M2.readLE a k := by
  simp only [List.append_assoc] at hF2 hF6
  simp only [W4Loop.lw, W4Loop.jw, List.append_assoc] at hF7 hF8
  have e2 := rd_step hF2 hLF2 hxd hh (out_S2 hw hK hzz hnz).1 (out_S2 hw hK hzz hnz).2
  have e4 := rd_step hF4 hLF4 hx2 hh (out_S4 hw hK hbp).1 (out_S4 hw hK hbp).2
  have e5 := rd_step hF5 hLF5 hx2 hh (out_S5 hw hK) trivial
  have e6 := rd_step hF6 hLF6 hx5 hh (out_S6 hw hK hz' hnz').1 (out_S6 hw hK hz' hnz').2
  have e7 := rd_step hF7 hLF7 hx5 hh (out_S7 hw hK hz'' hzz'').1 (out_S7 hw hK hz'' hzz'').2
  have e8 := rd_step hF8 hLF8 hx5 hh (out_S8 hw hK hzz'').1 (out_S8 hw hK hzz'').2
  exact ⟨e2, by rw [e8, e7, e6, e5, e4]⟩

theorem rnd_ge (k : Nat) : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega

/-- the function-level frame's complement, in arithmetic form -/
theorem final_out {R : RtInv} {s : State} {M : Memory} {sp K st zp zc a k : Nat}
    (ho : Outside a k (R.rt ++ winA s (K + 928) 112 ++ [(zp, zp + 8 * zc)] ++ stkWs M st))
    (hS : s.sp.toNat = sp + 928) (hKs : K ≤ sp) :
    Outside a k R.rt ∧ Zw sp K a k ∧ (a + k ≤ st ∨ st + 24 ≤ a) ∧
      (a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) ∧ (a + k ≤ zp ∨ zp + 8 * zc ≤ a) := by
  simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true, hS] at ho
  obtain ⟨⟨⟨h0, h1, h2⟩, h3⟩, h4, h5⟩ := ho
  exact ⟨h0, by simp only [Zw]; omega, h4, h5, h3⟩

theorem final_outL {M : Memory} {st zp zc a k : Nat} (ho : Outside a k ([(zp, zp + 8 * zc)] ++ stkWs M st)) :
    (a + k ≤ st ∨ st + 24 ≤ a) ∧ (a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a) ∧
      (a + k ≤ zp ∨ zp + 8 * zc ≤ a) := by
  simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at ho
  exact ⟨ho.2.1, ho.2.2, ho.1⟩

theorem zw_of_ap {sp K a k : Nat} (h : Apart a k (sp - K) (K + 1040)) (hKs : K ≤ sp) : Zw sp K a k := by
  unfold Apart at h; simp only [Zw]; omega

theorem zw_of_sep {L : List (Nat × Nat)} {sp K a k : Nat} (hLs : LiveSep L [(sp - K, sp + 1040)]) (h : InRanges a k L)
    (hKs : K ≤ sp) : Zw sp K a k := by
  have := W4Pro.apart_of_inRanges_sep hLs h (by omega)
  unfold Apart at this; simp only [Zw]; omega

theorem out9_p {sp st p q : Nat} (hw : Apart p q (sp - 4288) (4288 + 1040)) (hd : Apart p q st 24) (hs : 4288 ≤ sp) :
    Outside p q [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
  unfold Apart at hw hd; simp only [outside_cons, outside_nil, and_true]; omega

theorem out9_fresh {R : RtInv} {sp K st p q : Nat} (hLrt : LiveSep [(sp - K, sp + 1040)] R.rt) (hin : InRanges p q R.rt)
    (hd : p + q ≤ st ∨ st + 24 ≤ p) (hK : 4304 ≤ K) (hKs : K ≤ sp) :
    Outside p q [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := hLrt (sp - K, sp + 1040) (List.mem_singleton_self _)
  have h3 := MemFrame.outside_mem this hr
  simp only [outside_cons, outside_nil, and_true] at h3 ⊢
  omega

theorem natLive_tr {R : RtInv} {L L' : List (Nat × Nat)} {M M' : Memory} {p c : Nat} (h : NatLive M R L p c)
    (hx : LiveExt R L L') (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w) : NatLive M' R L' p c :=
  fun hc => ⟨(h hc).1, hx.held (h hc).2.1, by rw [hacc]; exact (h hc).2.2.1, (h hc).2.2.2⟩

theorem lvl_le {l r n : Nat} (h : l + r + 17 * n + 68 ≤ 2 ^ 16) : l + r ≤ 2 ^ 16 := by omega

theorem inv_fin {R : RtInv} {b g sp K st : Nat} {L : List (Nat × Nat)} {M M' : Memory}
    (hF : MemFrame M M' [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)])
    (hLrt : LiveSep [(sp - K, sp + 1040)] R.rt) (hst : Held R L st 24) (hK : 4304 ≤ K) (hKs : K ≤ sp)
    (h : R.inv b L g (view R.rt L M)) : R.inv b L g (view R.rt L M') := by
  have hw : Outside (sp - K) (sp + 1040 - (sp - K)) R.rt := hLrt _ (List.mem_singleton_self _)
  refine FvModexp.Expmc.inv_frame hF (fun r hr => ?_) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inr (hw.of_sub (by omega) (by omega))
  · exact Or.inr (hw.of_sub (by omega) (by omega))
  · exact Or.inr (hw.of_sub (by omega) (by omega))
  · exact hst.sub (by simp only; omega) (by simp only; omega)

/-- the result array: `z`'s or a fresh runtime object -/
theorem res_of {R : RtInv} {L L1 L2 L' : List (Nat × Nat)} {zp zc zp' zc' zzp zzc zp'' zc'' zzp'' zzc'' p c : Nat}
    (hor : (p = zzp'' ∧ c = zzc'') ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L'))
    (hP : (zp'' = zp' ∧ zc'' = zc' ∧ zzp'' = zzp ∧ zzc'' = zzc) ∨ (zp'' = zzp ∧ zc'' = zzc ∧ zzp'' = zp' ∧ zzc'' = zc'))
    (hzo : (zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L2))
    (hzz : InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L1)
    (x1 : LiveExt R L L1) (x2 : LiveExt R L L2) (x5 : LiveExt R L L') :
    (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L) := by
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · have hz' : (zp' = zp ∧ zc' = zc) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L) :=
      hzo.imp id fun h => ⟨h.1, apartAll_ext x2 h.2⟩
    rcases hP with ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · exact Or.inr ⟨hzz.1, apartAll_ext x1 hzz.2⟩
    · exact hz'
  · exact Or.inr ⟨hin, apartAll_ext x5 hap⟩

theorem norm_tr {M M' : Memory} {p l c : Nat} (hn : NatNorm M p l) (hl : l ≤ c)
    (hr : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k) : NatNorm M' p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact Or.inl h0
  rcases hn with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hr _ _ (by omega) (by omega)]; exact h)

theorem top_ne {M : Memory} {yp ylen : Nat} (h : NatNorm M yp ylen) (hy : 0 < ylen) :
    M.readLE (yp + 8 * (ylen - 1)) 8 ≠ 0 := by
  rcases h with h | h
  · omega
  · exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the function-level post of window-4** from the chain's post `EnPost` -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD g sp st zp zc xp xl xc yp ylen mp n mc : Nat}
    {s s' : State} (hP : EPre R b L K g sp st zp zc xp xl xc yp ylen mp n mc s)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1)
    (hE : EnPost R b L K g sp st zp zc xp xl yp ylen mp n mc costD s s') :
    (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    Post R b L K costD zp zc st xp xl yp ylen mp n s s' := by
  have hP' := hP
  obtain ⟨he, -, -, -, -, hn, -, -, -, hmO, -, -, hmN, hyO, -, -, hyN, hyl, -,
    -, -, -, -, -, -, -, -, -, -, hz, -, hsok, hstw, -, -, -, -, hstf, -, -⟩ := hP'
  have hspE := he.sp
  have hgE := he.g
  obtain ⟨hs1, hs28, -, -, -, -, -, hK, hKs, -, -, hLrt, hLs, -, -⟩ := he
  obtain ⟨Xv', hXm, hXB, M, L1, b1, hF0, hLF0, hx0, hb1, hkf0, hlen0, hcapM, l1, zzp, zzc, -, hl1b,
    ⟨hzzl, hzzin, hzzap⟩, Md, Ld, bd, rp, rl, rc, M1, rrp, rrc, onep, M2, L2, b2, ⟨hxd, hFd, hLFd, hlend, hkfd⟩, hbd,
    hlenD, -, hRR, hOC, hRet⟩ := hE
  have hF2 := hRR.1
  have hLF2 := hRR.2.1
  obtain ⟨hF3, hLF3, hx3, hb3, hsok3, hlen3, hkept3, hfresh3, -⟩ := hOC
  obtain ⟨Mj, M', zp', zc', L', b', hF4, hLF4, -, -, hZP, hZj⟩ := hRet
  obtain ⟨-, hzb', -, hx5, hb5, hF5, hLF5, -, -, hzo⟩ := hZP
  obtain ⟨M0z, zp'', zc'', zzp'', zzc'', Mx, hPz, hF6, hLF6, -, hBufs, -, hvx, hT⟩ := hZj
  obtain ⟨M'', Mj2, p, l, c, ⟨hF7, hLF7, -, -⟩, hzzv, hJ, hFin⟩ := hT
  obtain ⟨L'', b'', hx8, hb8, hinv8, -, hF8, hLF8, hval8, hlc, hc64, hnl8, hor8, -⟩ := hJ
  obtain ⟨hsp', h18', h28', h29', h0', h1', h2', hn0', hF9⟩ := hFin
  have xd := hx0.trans hxd
  have x2 := xd.trans hx3
  have x5 := x2.trans hx5
  have x8 := x5.trans hx8
  have hlc0 := hsok.2.2.2.2.2.1
  have hnz : n ≤ zzc := n_le_of hzzl
  have hnz' : n ≤ zc' := n_le_of2 hzb'.1
  have hK4 : 4304 ≤ K := hK
  -- the stack header through `divRet → oneJ` and the arrays
  have hh_st : Outside st 24 R.rt ∨ InRanges st 24 L := hsok.2.1.symm
  have hw_st : Zw sp K st 24 := hdr_zw hstw hKs
  have hF2' := hF2
  simp only [List.append_assoc] at hF2'
  have eM1 : M1.readLE st 24 = Md.readLE st 24 :=
    rd_step hF2' hLF2 xd hh_st (out_S2 hw_st hK4 (ap_fresh hzzin hzzap hx0 hh_st) hnz).1
      (out_S2 hw_st hK4 (ap_fresh hzzin hzzap hx0 hh_st) hnz).2
  have hd1 := hdr_fields eM1
  have kMd := akf_trans hkf0 hx0 hkfd
  have kM1 : (stW M1 st = stW s.mem st ∧ stCap M1 st = stCap s.mem st) ∨
      (InRanges (stW M1 st) (8 * stCap M1 st) R.rt ∧ ApartAll (stW M1 st) (8 * stCap M1 st) L) := by
    rw [hd1.1, hd1.2.2]; exact kMd
  have kM12 : (stW M2 st = stW M1 st ∧ stCap M2 st = stCap M1 st) ∨
      (InRanges (stW M2 st) (8 * stCap M2 st) R.rt ∧ ApartAll (stW M2 st) (8 * stCap M2 st) Ld) := by
    by_cases h : stLen M1 st + StackNat.rnd (17 * n) ≤ stCap M1 st
    · exact Or.inl (hkept3 h)
    · exact Or.inr (hfresh3 (Nat.lt_of_not_le h))
  have kM2 := akf_trans kM1 xd kM12
  have hlenM1 : stLen M1 st = l1 + 2 * StackNat.rnd (2 * n) := hd1.2.1.trans hlenD
  have hl0M : stLen s.mem st ≤ stLen M st := by rw [hlen0]; exact Nat.le_add_right _ _
  have hl0Md : stLen s.mem st ≤ stLen Md st := Nat.le_trans hl0M hlend
  have hl0M1 : stLen s.mem st ≤ stLen M1 st := by rw [hd1.2.1]; exact hl0Md
  have hl0L : stLen s.mem st ≤ l1 + 2 * StackNat.rnd (2 * n) := hlenM1 ▸ hl0M1
  have hcM2 : l1 + 2 * StackNat.rnd (2 * n) + 17 * n ≤ stCap M2 st :=
    lc_of (hlenM1 ▸ hlen3) (rnd_ge _) hsok3.2.2.2.2.2.1
  -- the zone of the function-level frame
  have zone : ∀ a k, (Outside a k R.rt ∨ InRanges a k L) → Zw sp K a k → (a + k ≤ st ∨ st + 24 ≤ a) →
      (a + k ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a) →
      (2 * n ≤ zc → a + k ≤ zp ∨ zp + 8 * zc ≤ a) →
      M0z.readLE a k = s.mem.readLE a k ∧ s'.mem.readLE a k = s.mem.readLE a k := by
    intro a k hh hw hd hf hzc
    have hzz := ap_fresh hzzin hzzap hx0 hh
    have hz' := z'_ap hzo x2 hh hzb'.1 hzc
    have hbb := bufs_ap hPz hz' hzz
    exact chainA hK4 hF0 hLF0 hx0 hFd hLFd xd hF2 hLF2 hF3 hLF3 x2 hF4 hLF4 hF5 hLF5 x5 hF6 hLF6 hF7 hLF7 hF8 hLF8
      hF9 hh hw hd (arr_ap hkf0 hh hf hl0M) hcapM hzz hnz (arr_ap kM1 hh hf hl0M1)
      (bp_ap (arr_ap kM2 hh hf hl0L) hcM2) hz' hnz' hbb.1 hbb.2
  have hacc : ∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF9.accessible, hF8.accessible, hF7.accessible, hF6.accessible, hF5.accessible, hF4.accessible,
      hF3.accessible, hF2.accessible, hFd.accessible, hF0.accessible]
  have hacc2 : ∀ a k w, s'.mem.accessible a k w = M2.accessible a k w := fun a k w => by
    rw [hF9.accessible, hF8.accessible, hF7.accessible, hF6.accessible, hF5.accessible, hF4.accessible]
  -- the header at the return
  have hf_st := free_ap hstf hlc0
  have hzz_st := ap_fresh hzzin hzzap hx0 hh_st
  have hz'_st := z'_ap hzo x2 hh_st hzb'.1 (fun h => ap_of' (hz h).1.2.2.1)
  have hbb_st := bufs_ap hPz hz'_st hzz_st
  have eHdr := (chainH hK4 xd hF2 hLF2 x2 hF4 hLF4 hF5 hLF5 x5 hF6 hLF6 hF7 hLF7 hF8 hLF8 hh_st hw_st hzz_st hnz
    (bp_ap (arr_ap kM2 hh_st hf_st hl0L) hcM2) hz'_st hnz' hbb_st.1 hbb_st.2).2
  have hdj := hdr_fields eHdr
  have eW : stW s'.mem st = stW M2 st := (hF9.readLE st 8 (out9_hdr hw_st hK4).1).trans hdj.1
  have eC : stCap s'.mem st = stCap M2 st := (hF9.readLE (st + 16) 8 (out9_hdr hw_st hK4).2).trans hdj.2.2
  have eL : stLen s'.mem st = stLen s.mem st := hn0'
  -- the result array at the return
  have h4288 : 4288 ≤ sp := Nat.le_trans (by decide) (Nat.le_trans hK4 hKs)
  have hout_p : Outside p (8 * c) [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 376, sp + 400), (st + 8, st + 16)] := by
    rcases hor8 with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · exact out9_p hBufs.2.1.2.2.2.2.2.1 (hBufs.2.2.2.2.2.2.2.2.2.2.2.2 _ (List.mem_cons_of_mem _
        (List.mem_singleton_self _))).2 h4288
    · exact out9_fresh hLrt hin (ap_fresh hin hap x5 hh_st).symm hK4 hKs
  have hrp : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → s'.mem.readLE a k = Mj2.readLE a k := fun a k h1 h2 =>
    hF9.readLE a k (hout_p.of_sub h1 h2)
  have hl' := Expmc.normL_le Mj2 p l
  -- the value
  have hmp := (zone mp (8 * n) hmO.1.symm (zw_of_ap hmO.2.1 hKs) (ap_of hmO.2.2.1) (free_ap hmO.2.2.2 hlc0)
    (fun h => ap_of' (hz h).2.2.2.2.2.1)).1
  have hval : natVal s'.mem p (Expmc.normL Mj2 p l) =
      natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n := by
    simp only [natVal]
    rw [hrp _ _ (Nat.le_refl _) (by have := Nat.mul_le_mul_left 8 (Nat.le_trans hl' hlc); omega),
      Expmc.normL_val]
    have hv8 : Mj2.readLE p (8 * l) = _ := hval8
    rw [hv8, hzzv, hvx, hmp, Expmc.readLE_wd s.mem yp (ylen - 1) ylen (by omega)]
    exact W4Pro.w4_value n _ _ Xv' _ ylen hn (Expmc.readLE_lt_B _ _ _) hMo hXm hXB hyl (Expmc.readLE_lt_B _ _ _)
      (W4Pro.y_ge s.mem yp ylen hyl (top_ne hyN hyl))
  refine ⟨⟨by rw [hsp', hs1], by rw [h28', hs28], h29', h18'⟩, p, Expmc.normL Mj2 p l, c, h0', h1', h2', hval,
    norm_tr (Expmc.normL_norm Mj2 p l) (Nat.le_trans hl' hlc) hrp, Nat.le_trans hl' hlc, hc64, L'', b'', x8, ?_,
    ?_, natLive_tr hnl8 (LiveExt.refl R L'') (fun a k w => hF9.accessible a k w),
    res_of hor8 hPz hzo ⟨hzzin, hzzap⟩ hx0 x2 x5, ?_, ?_, ?_⟩
  · show b - W4Cost n xl costD (stLen s.mem st) ≤ b''
    unfold W4Cost
    rw [hlenM1] at hb3
    exact bud_fin hb1 hbd hb3 hb5 hb8 (if_le n) (snc_mono (lvl_le hl1b))
  · rw [hgE]; exact inv_fin hF9 hLrt (x8.held hsok.2.1) hK4 hKs hinv8
  · refine ⟨⟨hsok.1, x8.held hsok.2.1, by rw [hacc]; exact hsok.2.2.1, hsok.2.2.2.1, ?_, ?_, ?_⟩, eL, ?_⟩
    · rw [eW, eC]; exact natLive_tr hsok3.2.2.2.2.1 (hx5.trans hx8) hacc2
    · rw [eL, eC]; exact Nat.le_trans hl0L (Nat.le_trans (Nat.le_add_right _ _) hcM2)
    · rw [eC]; exact hsok3.2.2.2.2.2.2
    · rw [eW, eC]; exact kM2
  · refine ⟨fun a k ho => ?_, fun a k w => hacc a k w⟩
    obtain ⟨h0, hw, hd, hf, hzc⟩ := final_out ho hspE hKs
    exact (zone a k (Or.inl h0) hw hd hf (fun _ => hzc)).2
  · refine ⟨fun a k hin ho => ?_⟩
    obtain ⟨hd, hf, hzc⟩ := final_outL ho
    exact (zone a k (Or.inr hin) (zw_of_sep hLs hin hKs) hd hf (fun _ => hzc)).2

end FvModexp.Arm64.ExpW4
