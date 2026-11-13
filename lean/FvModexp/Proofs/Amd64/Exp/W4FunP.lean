import FvModexp.Proofs.Amd64.Exp.W4En
import FvModexp.Proofs.Amd64.Exp.W4FunH

set_option autoImplicit false

/-!
# window-4 (amd64): the function-level pre/postcondition and the small lemmas of `post_of` (agent expmc s59)

`PreD` = the entry facts `W4En.EPre` WITHOUT the return-address conjuncts (`[RSP] = r`, `r < 2^47`: the caller's return
address is not constrained beyond the ABI; `EPre_of` re-adds them from `RetAddr`), `m` odd and `> 1`, and the budget
`enStep` needs. `PostD` = the results `RAX/RBX/RCX`, the value `x^y mod m` (normalised), the live set / budget / stack /
frame facts. The arithmetic side facts of `post_of` are tiny lemmas here (no `omega` in the post context, s55/s58).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpW4

open FvModexp.Amd64.W4En (EPre EEnv OE XnB free)
open FvModexp.Amd64.W4Pro (Zw)

/-- `W4En.EPre` without the return-address conjuncts (and with `RBP` free) -/
def EPreA (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (g fs sp st zp zc xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - 8 - K, sp + 0x3f8)] ∧ Outside W4En.wTy 16 R.rt ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  OE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  OE R L sp K st s.mem yp (8 * ylen) ∧ s.mem.accessible yp (8 * ylen) false = true ∧ yp + 8 * ylen ≤ 2 ^ 48 ∧
    NatNorm s.mem yp ylen ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  OE R L sp K st s.mem xp (8 * xc) ∧ s.mem.accessible xp (8 * xc) false = true ∧ xp + 8 * xc ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ 0 < xl ∧ xl ≤ 128 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (2 * n ≤ zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart (fs - 8) 8 zp (8 * zc) ∧ Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - 8 - K) (K + 0x400) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x400) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  Apart st 24 StackNat.wbA 4 ∧ Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  s.mem.readLE (sp + 0x390) 8 = yp ∧ s.mem.readLE (sp + 0x398) 8 = ylen ∧ s.mem.readLE (sp + 0x3a8) 8 = mp ∧
  s.mem.readLE (sp + 0x3b0) 8 = n ∧ s.mem.readLE (sp + 0x3b8) 8 = mc ∧
  R.inv b L g (view R.rt L s.mem)

/-- `EPre` from `EPreA` and the ABI's return-address facts -/
theorem EPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st zp zc xp xl xc yp ylen mp n mc r : Nat}
    {s : State} (h : EPreA R b L K g fs sp st zp zc xp xl xc yp ylen mp n mc s)
    (hr : s.mem.readLE (sp + 0x388) 8 = r) (hr47 : r < 2 ^ 47) :
    EPre R b L K g fs sp st (s.regs 5).toNat r zp zc xp xl xc yp ylen mp n mc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a42, a43, a44, a45, a46, a47⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, rfl, hr, hr47, a42, a43, a44, a45, a46,
    a47⟩

/-- the precondition: the entry facts (frame `sp = RSP - 0x388`, window `[sp - 8 - K, sp + 0x3f8)`), `m` odd and
`> 1`, the closed budget (`XnB`: the division cost `costD` bounds `costF` on every level the window reaches) -/
def PreD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) : Prop :=
  EPreA R b L K (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x388) st zp zc xp xl xc yp ylen mp n mc s ∧
  st ≠ 0 ∧ natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧
  XnB costF n costD (stLen s.mem st + StackNat.rnd (23 * n)) xl (b - stackNatCost (stLen s.mem st) (23 * n)) ∧
  stackNatCost (stLen s.mem st) (23 * n) ≤ b

/-- the postcondition (results `RAX`, `RBX`, `RCX`), with the goroutine `g` explicit -/
@[reducible] def PostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD g zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - W4Pro.W4Cost n xl costD (stLen s.mem st) ≤ b' ∧
      R.inv b' L' g (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s (K + 0x390) 0x70 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- the postcondition: `FS` base and `DF` kept, and `PostG` -/
def PostD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ PostG R b L K costD (s.regs 14).toNat zp zc st xp xl yp ylen mp n s s'

/-! ## the small lemmas -/

/-- **the enlarged live set stays clear of the frame window**: new objects are runtime memory, the window is not -/
theorem sepL1 {R : RtInv} {L L1 : List (Nat × Nat)} {sp K : Nat} (hx : LiveExt R L L1)
    (hrt : Outside (sp - 8 - K) (K + 0x400) R.rt) (hLs : LiveSep L [(sp - 8 - K, sp - 8 + 0x400)]) (hs : 8 ≤ sp) :
    LiveSep L1 [(sp - 8 - K, sp + 0x3c0)] :=
  hx.liveSep (W4En.liveSep_sub' hLs (Nat.le_refl _) (by omega)) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hrt.of_sub (by simp only; omega) (by simp only; omega)

theorem k8_of {K sp : Nat} (h : K ≤ sp - 8) (hK : 41512 ≤ K) : K + 8 ≤ sp := by omega
theorem k4_of {K : Nat} (hK : 41512 ≤ K) : 4296 ≤ K := by omega
theorem sp_lt {sp : Nat} (h : sp - 8 + 0x400 ≤ 2 ^ 48) : sp + 0x388 < 2 ^ 64 := by omega
theorem sp_sub {sp : Nat} : sp + 0x388 - 0x388 = sp := by omega
theorem le_rnd (k : Nat) : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega

theorem free_ap {M : Memory} {st a k : Nat} (h : Apart a k (free M st).1 (free M st).2)
    (hl : stLen M st ≤ stCap M st) :
    a + k ≤ stW M st + 8 * stLen M st ∨ stW M st + 8 * stCap M st ≤ a := by
  simp only [free] at h; unfold Apart at h; omega

theorem ap_of {a k x y : Nat} (h : Apart a k x y) : a + k ≤ x ∨ x + y ≤ a := h
theorem ap_of' {a k x y : Nat} (h : Apart x y a k) : a + k ≤ x ∨ x + y ≤ a := by unfold Apart at h; omega

theorem bp_ap {a k W l c n : Nat} (h : a + k ≤ W + 8 * l ∨ W + 8 * c ≤ a) (hc : l + 17 * n ≤ c) :
    a + k ≤ W + 8 * l ∨ W + 8 * l + 8 * (17 * n) ≤ a := by omega

theorem lc_of {l c c' n : Nat} (h1 : c' = l + StackNat.rnd (17 * n)) (h3 : c' ≤ c) : l + 17 * n ≤ c := by
  have := le_rnd (17 * n); omega

theorem n_le_of {n z : Nat} (h : 2 * n + 1 ≤ z) : n ≤ z := by omega
theorem n_le_of2 {n z : Nat} (h : 2 * n ≤ z) : n ≤ z := by omega
theorem le_of_eq_add {a b c : Nat} (h : a = b + c) : b ≤ a := by omega

/-- `z`'s array after `z.make`: the old one (when `2n ≤ cap`) or fresh -/
theorem z1_ap {R : RtInv} {L L2 : List (Nat × Nat)} {zp zc zp' zc' n a k : Nat} {e : Prop}
    (hzo : (zp' = zp ∧ zc' = zc ∧ e) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L2))
    (hx : LiveExt R L L2) (hh : Outside a k R.rt ∨ InRanges a k L) (h2n : 2 * n ≤ zc')
    (hz : 2 * n ≤ zc → a + k ≤ zp ∨ zp + 8 * zc ≤ a) : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a := by
  rcases hzo with ⟨rfl, rfl, -⟩ | ⟨hin, hap⟩
  · exact hz h2n
  · exact W4Pro.ap_fresh hin hap hx hh

/-- the second `make` (of `zz`): the lsh layer's fresh `zz` or a fresher one -/
theorem zz2_of {R : RtInv} {L1 La : List (Nat × Nat)} {zzp zzc zzp2 zzc2 : Nat} {e : Prop}
    (hz : (zzp2 = zzp ∧ zzc2 = zzc ∧ e) ∨ (InRanges zzp2 (8 * zzc2) R.rt ∧ ApartAll zzp2 (8 * zzc2) La))
    (hin : InRanges zzp (8 * zzc) R.rt) (hap : ApartAll zzp (8 * zzc) L1) (hx : LiveExt R L1 La) :
    InRanges zzp2 (8 * zzc2) R.rt ∧ ApartAll zzp2 (8 * zzc2) L1 := by
  rcases hz with ⟨rfl, rfl, -⟩ | ⟨hin2, hap2⟩
  · exact ⟨hin, hap⟩
  · exact ⟨hin2, W4Pro.apartAll_old hx hap2⟩

/-- the loop's buffers are `z'` and `zz'` (in some order) -/
theorem bufs_ap {zp' zc' zzp zzc zp'' zc'' zzp'' zzc'' a k : Nat}
    (hP : (zp'' = zp' ∧ zc'' = zc' ∧ zzp'' = zzp ∧ zzc'' = zzc) ∨ (zp'' = zzp ∧ zc'' = zzc ∧ zzp'' = zp' ∧ zzc'' = zc'))
    (h1 : a + k ≤ zp' ∨ zp' + 8 * zc' ≤ a) (h2 : a + k ≤ zzp ∨ zzp + 8 * zzc ≤ a) :
    (a + k ≤ zp'' ∨ zp'' + 8 * zc'' ≤ a) ∧ (a + k ≤ zzp'' ∨ zzp'' + 8 * zzc'' ≤ a) := by
  rcases hP with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

/-- the normalised `x` is below `B^n` -/
theorem xv_lt {M : Memory} {xp xl n Mv Xv : Nat} (h : (xl ≤ n ∧ Xv = M.readLE xp (8 * xl)) ∨ Xv = M.readLE xp (8 * xl) % Mv)
    (hm : 0 < Mv) (hmB : Mv < Exp.B ^ n) : Xv < Exp.B ^ n := by
  rcases h with ⟨hl, rfl⟩ | rfl
  · exact Nat.lt_of_lt_of_le (Expmc.readLE_lt_B M xp xl) (Nat.pow_le_pow_right Exp.B_pos hl)
  · exact Nat.lt_trans (Nat.mod_lt _ hm) hmB

theorem xv_mod {X Xv Mv : Nat} {e : Prop} (h : (e ∧ Xv = X) ∨ Xv = X % Mv) : Xv % Mv = X % Mv := by
  rcases h with ⟨-, rfl⟩ | rfl
  · rfl
  · exact Nat.mod_mod _ _

theorem cap_pos {l c n : Nat} (h : l + 17 * n ≤ c) (hn : 0 < n) : 0 < c := by omega
theorem pos_of_lt {a : Nat} (h : 1 < a) : 0 < a := by omega
theorem fs_eq {s s' : State} (h : s'.fsBase.toNat = s.fsBase.toNat) : s'.fsBase = s.fsBase := BitVec.eq_of_toNat_eq h

end FvModexp.Amd64.ExpW4
