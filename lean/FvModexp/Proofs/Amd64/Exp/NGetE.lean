import FvModexp.Proofs.Amd64.Exp.NStkNilE
import FvModexp.Proofs.Common.StkPool
import FvModexp.Proofs.Amd64.Exp.NDefs

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the `sync.(*Pool).Get(&stackPool)` call (nat.go:287) (agent expmc s74; twin of
`Arm64.ExpN.getCallE`, adapted from top's Amd64/NatQ/DivMGet.lean `getCallM`)

`getCallE`: at the `Get` entry `X` (`RSP = t - 0x110`, `t` = expNN's entry `RSP` = `sp + 0x498`; callee window
`[t - 0x110 - 4096, t - 0x110) ∪ [t - 0x108, t - 0x100)` inside expNN's window `[sp - K, sp + 0x510)`), the contract
`PoolGetLive` (on `LibNE`), in continuation form: the pool was empty (`RAX = RBX = 0`) or gave a pooled `*stack`
(`RAX = type:*big.stack`, `RBX = d`, `StkSh`, fresh ranges `rs` added to the live set).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `Pool.Get` call** at its entry `X` (`RSP = t - 0x110`), in continuation form -/
theorem getCallE (impl : List Amd64.Segment) (R : RtInv)
    (hget : PoolGetLive (LibNE.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (Q : Amd64.Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp : Nat) (M : Janus.Arm64.Memory)
    (hal : sp % 8 = 0) (hK : 41640 ≤ K) (hKs : K ≤ sp) (hsp2 : sp + 0x510 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - K) (K + 0x510) true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + K < sp)
    (hwrt : Outside (sp - K) (K + 0x510) R.rt) (hgw : Apart (g + 16) 8 (sp - K) (K + 0x510))
    (hLs : LiveSep L [(sp - K, sp + 0x510)]) (hsv : RunIface.Serves R)
    (hnew0 : M.readLE (Free.poolA + newOffset) 8 = 0) (hinv : R.inv b L g (view R.rt L M))
    (X : State) (hpc : X.rip = BitVec.ofNat 64 (cA "sync.(*Pool).Get"))
    (hx4 : X.regs 4 = BitVec.ofNat 64 (sp + 0x388)) (hx14 : X.regs 14 = BitVec.ofNat 64 g)
    (hx0 : X.regs 0 = BitVec.ofNat 64 Free.poolA) (hmem : X.mem = M) (hXr : M.readLE (sp + 0x388) 8 = getR)
    (K' : ∀ (S' : State) (m : Janus.Arm64.Memory), S'.rip = BitVec.ofNat 64 getR →
      S'.regs 4 = BitVec.ofNat 64 (sp + 0x390) →
      S'.regs 5 = X.regs 5 → S'.regs 14 = X.regs 14 → S'.xmm 15 = X.xmm 15 → S'.fsBase = X.fsBase →
      S'.df = X.df → S'.mem = m →
      MemFrame M m (R.rt ++ [(sp + 0x388 - 4096, sp + 0x388), (sp + 0x390, sp + 0x398)]) →
      LiveFrame M m L [] → m.regions = M.regions →
      ((S'.regs 0 = 0#64 ∧ S'.regs 3 = 0#64 ∧ R.inv b L g (view R.rt L m)) ∨
        ∃ (d : Nat) (rs : List (Nat × Nat)), S'.regs 0 = BitVec.ofNat 64 Free.stkT ∧ S'.regs 3 = BitVec.ofNat 64 d ∧
          d < 2 ^ 64 ∧ StkSh m d rs ∧ FreshFrom rs L ∧ (∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) ∧
          LiveSep rs [(sp + 0x388 - 4096, sp + 0x388), (sp + 0x390, sp + 0x398)] ∧
          R.inv b (L ++ rs) g (view R.rt (L ++ rs) m)) →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibNE.program.link impl).withExit ret0) X Q := by
  unfold Apart at hgw
  have esp : (X.regs 4).toNat = sp + 0x388 := by rw [hx4, BitVec.toNat_ofNat]; omega
  have eg : (X.regs 14).toNat = g := by rw [hx14, BitVec.toNat_ofNat]; omega
  have e0 : (X.regs 0).toNat = Free.poolA := by rw [hx0, BitVec.toNat_ofNat]; decide
  have hcs : calleeStack64 X 4096 1 = [(sp + 0x388 - 4096, sp + 0x388), (sp + 0x390, sp + 0x398)] := by
    simp only [calleeStack64, esp]
  subst hmem
  have hpre : CallOK64 X 4096 1 ∧ StackRoom64 X 4096 1 ∧ X.mem.readLE ((X.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R (cA "sync.(*Pool).Get") [(X.regs 0).toNat] L b 0 (X.regs 14).toNat X.mem (liveWin64 X 4096 1) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hsv.2.2.2.2.2.2.2.1 _, ?_, Nat.zero_le _, ?_, ?_⟩
    · rw [esp, hXr]; decide
    · rw [esp]; omega
    · rw [esp]; omega
    · rw [esp]; omega
    · rw [esp]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
    · rw [eg]; omega
    · rw [eg]; exact hg2
    · rw [eg, esp]; omega
    · rw [hcs, eg]; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [e0]; exact hnew0
    · rw [eg]; exact hinv
    · intro r hr; have := hLs r hr
      simp only [liveWin64, hcs, esp, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true] at this ⊢
      omega
    · intro r hr
      simp only [liveWin64, hcs, esp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hwrt.of_sub (by simp only; omega) (by simp only; omega)
  refine Reaches.call_regions ((hget L b).withExit hret) hpc hpre fun s1 hpc1 hpost hrg => ?_
  obtain ⟨r, x, y, fl, m, zh, kr, hs1, hMF, hLF, hNew, hcase⟩ := hpost
  rw [hcs] at hMF
  rw [eg] at hcase
  have hrg' : m.regions = X.mem.regions := by rw [← hrg, hs1]
  subst hs1
  have hra : retAddrOf X = BitVec.ofNat 64 getR := by simp only [retAddrOf, esp, hXr]
  refine K' _ m (by rw [hpc1, hra]) (by simp only [MapAmd64.keepABI_apply, ↓reduceIte, hx4]; bv_omega)
    (by simp only [MapAmd64.keepABI_apply]; simp) (by simp only [MapAmd64.keepABI_apply]; simp)
    (by simp only [MapAmd64.keepX15_apply, ↓reduceIte]) rfl rfl rfl hMF hLF hrg' ?_
  rcases hcase with ⟨hr0, hr1, hinv1⟩ | ⟨rs, hr0, hSh, hfr, hin, hsep, hinv1⟩
  · refine Or.inl ⟨?_, ?_, hinv1⟩
    · simp only [MapAmd64.keepABI_apply]; exact BitVec.eq_of_toNat_eq (by simpa using hr0)
    · simp only [MapAmd64.keepABI_apply]; exact BitVec.eq_of_toNat_eq (by simpa using hr1)
  · rw [liveWin64, hcs] at hsep
    refine Or.inr ⟨(r 3).toNat, rs, ?_, ?_, (r 3).isLt, hSh, hfr, hin, fun q hq => ?_, hinv1⟩
    · simp only [MapAmd64.keepABI_apply, Nat.reduceEqDiff, ↓reduceIte, or_self]
      exact BitVec.eq_of_toNat_eq (by rw [hr0]; rfl)
    · simp only [MapAmd64.keepABI_apply]; simp
    · have := hsep q hq; simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at this ⊢
      exact ⟨this.1, this.2.1⟩

end FvModexp.Amd64.ExpN
