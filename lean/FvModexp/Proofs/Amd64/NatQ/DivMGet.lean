import FvModexp.Proofs.Amd64.Nat.DivMStk
import FvModexp.Proofs.Amd64.Nat.Free
import FvModexp.Proofs.Amd64.NatQ.DivMBase

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, `u ≥ v`: `getStack()` = `sync.(*Pool).Get(&stackPool)` (natdiv.go:538-539, nat.go:287) (top s40)

Twin of Arm64/Nat/DivMGet.lean. `nilGM`: from `nat.cmp`'s return (`AtC`, `cmp ≥ 0`, `stk` slot `RSP + 80 = 0`):
`TESTQ AX; JGE`, `MOVQ 0x138(SP), DX; TESTQ DX; JE`, `LEAQ stackPool, AX; CALL sync.(*Pool).Get` (return address
`getR = fn + 0x37e` pushed at `RSP - 240`). `getPreM`: the `PoolAmd64.PoolGetLive` precondition there (callee window
`[RSP - 4336, RSP - 240) ∪ [RSP - 232, RSP - 224)` inside `nat.div`'s window `[RSP - 41512, RSP + 112)`).
`getCallM`: the call, in continuation form: `KN` (the pool was empty: `RAX = RBX = 0`) or `KT` (a pooled `*stack`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

/-- the return point of the `Pool.Get` call (`fn + 0x37e`) -/
abbrev getR : Nat := 0x5ee25e
/-- the return point of the `newobject(type:big.stack)` call (`fn + 0x39d`) -/
abbrev noR : Nat := 0x5ee27d
/-- the join of the two `getStack()` outcomes (`RBX` = the stack; `fn + 0x3a0`) -/
abbrev joinA : Nat := 0x5ee280

theorem sp240' {s X : State} (hsp : X.regs 4 = s.regs 4 - 240#64) (h0 : 41512 ≤ (s.regs 4).toNat) :
    (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
  rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `stk == nil`: from `nat.cmp`'s return (`u ≥ v`) to the `Pool.Get` entry -/
theorem nilGM (impl : List Amd64.Segment) {zp zl zc z2 z2l z2c u ul uc v vl vc : Nat} {s : State} {S : State}
    (hS : AtC zp zl zc 0 z2 z2l z2c u ul uc v vl vc s S) (c : Nat) (hc : c ≤ 1)
    (hr0 : S.regs 0 = BitVec.ofNat 64 c)
    (hb' : 41512 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true) (Q : State → Prop)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 (cA "sync.(*Pool).Get") → X.regs 4 = s.regs 4 - 240#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.xmm 15 = 0#128 →
      X.df = false → X.regs 0 = BitVec.ofNat 64 Free.poolA →
      MemFrame S.mem X.mem [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232)] →
      X.mem.readLE ((s.regs 4).toNat - 240) 8 = getR →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q := by
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hS.mf.accessible]; exact hw
  have m4 := hS.s4
  have hc' : (c = 0 ∨ c = 1) := by omega
  clear hS
  rcases hc' with rfl | rfl
  all_goals janus64_run [hr0, m4, BitVec.msb_eq_decide] until [cA "sync.(*Pool).Get"]
  all_goals refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus_frame) ?_
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hfs | exact hx15 | exact hdf
    | (simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same]; rfl)
    | (janus64_simp; bv_omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the `Pool.Get` call** at its entry `X` (`RSP = sp - 240`), in continuation form -/
theorem getCallM (impl : List Amd64.Segment) (R : RtInv)
    (hget : PoolGetLive (LibDiv.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (b : Nat) (L : List (Nat × Nat)) (s : State) (hce : CallEnv R L s 41512 112) (hsv : RunIface.Serves R)
    (hpg : RunIface.PoolG R s.mem (win s 41512 112)) (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem))
    (X : State) (hpc : X.rip = BitVec.ofNat 64 (cA "sync.(*Pool).Get")) (hx4 : X.regs 4 = s.regs 4 - 240#64)
    (hx14 : X.regs 14 = s.regs 14) (hx0 : X.regs 0 = BitVec.ofNat 64 Free.poolA)
    (hXF : MemFrame s.mem X.mem (win s 41512 112)) (hXr : X.mem.readLE ((s.regs 4).toNat - 240) 8 = getR)
    (ret0 : BitVec 64) (Q : State → Prop)
    (K : ∀ (S' : State) (m : Janus.Arm64.Memory), S'.rip = BitVec.ofNat 64 getR → S'.regs 4 = s.regs 4 - 232#64 →
      S'.regs 5 = X.regs 5 → S'.regs 14 = s.regs 14 → S'.xmm 15 = X.xmm 15 → S'.fsBase = X.fsBase →
      S'.df = X.df → S'.mem = m →
      MemFrame X.mem m (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
        ((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)]) →
      LiveFrame X.mem m L [] → m.regions = X.mem.regions →
      ((S'.regs 0 = 0#64 ∧ S'.regs 3 = 0#64 ∧ R.inv b L (s.regs 14).toNat (view R.rt L m)) ∨
        ∃ (d : Nat) (rs : List (Nat × Nat)), S'.regs 0 = BitVec.ofNat 64 Free.stkT ∧ S'.regs 3 = BitVec.ofNat 64 d ∧
          d < 2 ^ 64 ∧ StkSh m d rs ∧ FreshFrom rs L ∧ (∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) ∧
          LiveSep rs [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
            ((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)] ∧
          R.inv b (L ++ rs) (s.regs 14).toNat (view R.rt (L ++ rs) m)) →
      ReachesRet (LibDiv.program.link impl) ret0 S' Q) :
    ReachesRet (LibDiv.program.link impl) ret0 X Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  unfold Apart at hga
  obtain ⟨-, hnw0, -, hnwW⟩ := hpg
  simp only [win, outside_cons, outside_nil, and_true] at hnwW
  have esp : (X.regs 4).toNat = (s.regs 4).toNat - 240 := sp240' hx4 hb'
  have eg : (X.regs 14).toNat = (s.regs 14).toNat := by rw [hx14]
  have e0 : (X.regs 0).toNat = Free.poolA := by rw [hx0, BitVec.toNat_ofNat]; decide
  have hcs : calleeStack64 X 4096 1 = [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
      ((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)] := by
    simp only [calleeStack64, esp]
    rw [show (s.regs 4).toNat - 240 + 8 = (s.regs 4).toNat - 232 by omega,
      show (s.regs 4).toNat - 232 + 8 * 1 = (s.regs 4).toNat - 224 by omega]
  have hXa : ∀ a k w, X.mem.accessible a k w = s.mem.accessible a k w := hXF.accessible
  have hXg : X.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hXF.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hinvX : R.inv b L (s.regs 14).toNat (view R.rt L X.mem) :=
    FvModexp.Amd64.NatAdd.inv_win hXF hout hb' hinv
  have hpre : CallOK64 X 4096 1 ∧ StackRoom64 X 4096 1 ∧ X.mem.readLE ((X.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R (cA "sync.(*Pool).Get") [(X.regs 0).toNat] L b 0 (X.regs 14).toNat X.mem (liveWin64 X 4096 1) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hsv.2.2.2.2.2.2.2.1 _, ?_, Nat.zero_le _, ?_, ?_⟩
    · rw [esp, hXr]; decide
    · rw [esp]; omega
    · rw [esp]; omega
    · rw [esp]; omega
    · rw [esp, hXa]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [eg]; omega
    · rw [eg, hXa]; exact hg2
    · rw [eg, esp, hXg]; omega
    · rw [hcs, eg]; simp only [outside_cons, outside_nil, and_true]; omega
    · rw [e0, hXF.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)]; exact hnw0
    · rw [eg]; exact hinvX
    · intro r hr; have := hLs r hr
      simp only [liveWin64, hcs, esp, win, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true] at this ⊢
      omega
    · intro r hr
      simp only [liveWin64, hcs, esp, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  refine ReachesRet.call_regions (hget L b) hpc hpre fun s1 hpc1 hpost hrg => ?_
  obtain ⟨r, x, y, fl, m, zh, kr, hs1, hMF, hLF, hNew, hcase⟩ := hpost
  rw [hcs] at hMF
  rw [eg] at hcase
  have hrg' : m.regions = X.mem.regions := by rw [← hrg, hs1]
  subst hs1
  have hra : retAddrOf X = BitVec.ofNat 64 getR := by simp only [retAddrOf, esp, hXr]
  refine K _ m (by rw [hra]) (by simp only [MapAmd64.keepABI_apply, ↓reduceIte, hx4]; bv_omega)
    (by simp only [MapAmd64.keepABI_apply]; simp) (by simp only [MapAmd64.keepABI_apply]; simp [hx14])
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

end FvModexp.Amd64.Q.NatDiv
