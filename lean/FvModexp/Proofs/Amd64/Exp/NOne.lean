import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Amd64.Nat.WordTData
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): the two `return z.setWord(1)` paths (`x == 1`: fn+0x14c, `y == 0`: fn+0x802) (agent expmc s66;
twin of `Arm64.ExpN.one`)

`z.setWord(1)` (nat.go:74-79) = `z.make(1)` (reuse when `cap z ≠ 0`, else `makeslice(Word, 1, 1)`, return fn+0x166 /
fn+0x81c, pushed at `t - 0x110`), `z[0] = 1`; the result `(p, 1, c)` is stored to the result slots (`t - 0x58 …
t - 0x40`) and returned (`ADDQ $0x100, SP; POPQ BP; RET`). Continuation form: `FA` (reuse) / `FB` (fresh block, the
contract's raw facts). Entry `RSP = t - 0x108`, `t = sp + 0x498`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `return z.setWord(1)` from `pc0 ∈ {fn+0x14c, fn+0x802}` (`RSP = t - 0x108`, `z = (zp, zc)` in `RAX`/`RCX`) -/
theorem one (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibN.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g fs t bp zp zc pc0 : Nat) (M : Janus.Arm64.Memory)
    (hpc0 : pc0 = 6189292 ∨ pc0 = 6191010) (hce : CallW.CEnv R L g fs (t - 0x498) K 0x510 M) (hK : 4400 ≤ K)
    (ht : 0x498 ≤ t) (hty : Outside StackNat.wT 16 R.rt)
    (hzc : zc < 2 ^ 64) (hzp : zp < 2 ^ 64)
    (hz : 0 < zc → M.accessible zp 8 true = true ∧ zp + 8 ≤ 2 ^ 48 ∧ Apart zp 8 (t - 0x498 - K) (K + 0x510))
    (hok : zc = 0 → R.ok (Extracted.program.contractAddr "runtime.makeslice") [StackNat.wT, 1, 1] ∧
      blockSize 8 true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (rbp : M.readLE (t - 8) 8 = bp) (rra : M.readLE t 8 = ret0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 pc0) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hmem : S.mem = M)
    (FA : 0 < zc → ∀ s' : State, s'.regs 4 = BitVec.ofNat 64 (t + 8) → s'.regs 5 = BitVec.ofNat 64 bp →
      s'.regs 0 = BitVec.ofNat 64 zp → s'.regs 3 = 1#64 → s'.regs 1 = BitVec.ofNat 64 zc →
      s'.regs 14 = BitVec.ofNat 64 g → s'.fsBase = S.fsBase → s'.df = S.df → s'.xmm 15 = S.xmm 15 →
      MemFrame M s'.mem [(zp, zp + 8), (t - 0x58, t - 0x40)] →
      s'.mem.readLE zp 8 = 1 → s'.mem.regions = M.regions → F s')
    (FB : zc = 0 → ∀ (s' : State) (p r : Nat) (m : Janus.Arm64.Memory),
      LiveFrame M m L [] →
      MemFrame M m (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24), (t - 0x110, t - 0x108)]) →
      m.regions = M.regions → ApartAll p r L → InRanges p r R.rt → p + r ≤ 2 ^ 48 → M.accessible p r true = true →
      p % 8 = 0 → 8 ≤ r → r = blockSize 8 true → R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m) →
      s'.regs 4 = BitVec.ofNat 64 (t + 8) → s'.regs 5 = BitVec.ofNat 64 bp →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = 1#64 → s'.regs 1 = 1#64 →
      s'.regs 14 = BitVec.ofNat 64 g → s'.fsBase = S.fsBase → s'.df = S.df → s'.xmm 15 = S.xmm 15 →
      MemFrame m s'.mem [(p, p + 8), (t - 0x58, t - 0x40)] →
      s'.mem.readLE p 8 = 1 → s'.mem.regions = M.regions → F s') :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hce0 := hce
  obtain ⟨hal, hK0, hA0, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have es1 : BitVec.ofNat 64 (t - 0x108) + 256#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  subst hmem
  by_cases hc : 0 < zc
  · obtain ⟨hza, hz48, hzw⟩ := hz hc
    unfold Apart at hzw
    have bzc : (BitVec.ofNat 64 zc = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this; omega
    have rbp' : (S.mem.writeLE zp 8 1).readLE (t - 8) 8 = bp := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rbp
    have rra' : (S.mem.writeLE zp 8 1).readLE t 8 = ret0 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact rra
    rcases hpc0 with rfl | rfl
    all_goals
      janus64_run [es1, es2, es3, bzc, rbp, rra, rbp', rra']
      all_goals refine FA hc _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
      all_goals first | janus_frame | rfl
  · have hc0 : zc = 0 := by omega
    obtain ⟨hok1, hbs⟩ := hok hc0
    subst hc0
    have bzc : (BitVec.ofNat 64 0 = 0#64) = True := by simp
    have hwt : Apart StackNat.wT 16 (t - 0x498 - K) (K + 0x510) := apart_of_data hd 1 (by decide) (by decide) hwacc
    janus_eval_nat h_t : StackNat.wT
    rw [h_t] at hok1 hwt hty
    unfold Apart at hwt
    obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
    have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
        ([(t - 0x110 - 4096, t - 0x110), (t - 0x110 + 8, t - 0x110 + 8 + 24)] ++ [(t - 0x110, t - 0x110 + 8)]) := by
      intro r hr
      have := hLs r hr
      simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
      omega
    have hgA : g + 16 + 8 ≤ t - 264 - 8 - 4096 ∨ t - 264 - 8 ≤ g + 16 := by unfold Apart at hgw; omega
    have hgB : g + 16 ≤ t - 264 - 8 ∨ t - 264 - 8 + 16 ≤ g := by unfold Apart at hgw; omega
    have hg3' : ∀ v, (S.mem.writeLE (t - 264 - 8) 8 v).readLE (g + 16) 8 + 4096 < t - 264 - 8 := by
      intro v; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at hgw; omega)]; omega
    have q1 := hg3' 6189318; have q2 := hg3' 6191036
    rcases hpc0 with rfl | rfl
    all_goals
      janus64_run [es1, es2, es3, bzc, hws, hwp, BitVec.msb_eq_decide, rbp, rra] until [6189318, 6191036] calls [hmk.pos]
      rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ _ _ hinv' _ hpw1 _
      unfold Apart at hpw1
      have hwr : ∀ v, MemFrame S.mem (S.mem.writeLE (t - 264 - 8) 8 v) [(t - 0x110, t - 0x108)] := fun v => by janus_frame
      have hLw : ∀ v, LiveFrame S.mem (S.mem.writeLE (t - 264 - 8) 8 v) L [] := fun v =>
        (LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
      have hF : MemFrame S.mem m (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24),
          (t - 0x110, t - 0x108)]) := by
        refine (hwr _).trans hMF fun a k ho => ?_
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        refine ⟨by omega, ho.1, by omega, by omega⟩
      have hra : Outside t 8 (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24),
          (t - 0x110, t - 0x108)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
      have hrb : Outside (t - 8) 8 (R.rt ++ [(t - 0x110 - 4096, t - 0x110), (t - 0x108, t - 0x108 + 24),
          (t - 0x110, t - 0x108)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
      have rra2 : (m.writeLE ptr.toNat 8 1).readLE t 8 = ret0 := by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hF.readLE _ _ hra]; exact rra
      have rbp2 : (m.writeLE ptr.toNat 8 1).readLE (t - 8) 8 = bp := by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hF.readLE _ _ hrb]; exact rbp
      janus64_run [es1, es2, es3, rra2, rbp2]
      all_goals
        (refine FB rfl _ ptr.toNat 8 m ((hLw _).trans hLF fun _ _ h => h) hF hrg1 hAp hIn (by omega)
            hacc h8 (Nat.le_refl _) rfl hinv' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      all_goals first | (janus64_simp; done) | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
      all_goals first | janus_frame | rfl | (simp only [Janus.Arm64.Memory.regions_writeLE]; exact hrg1)

end FvModexp.Amd64.ExpN
