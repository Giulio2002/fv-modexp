import FvModexp.Proofs.Amd64.Exp.LibOdd
import FvModexp.Proofs.Amd64.Exp.W4FunE
import FvModexp.Proofs.Amd64.Exp.W2FunE

set_option autoImplicit false

/-!
# `nat.expNNOdd` (amd64): statement layer and the windows' entry facts (agent expmc s64; twin of `Arm64.OddDefs`)

`z.expNNOdd(stk, x, y, m)` (nat.go:1343-1358, fn = 0x5eaf40): stack check, `PUSHQ BP`, `SUBQ $0x68` (frame
`f = RSP - 0x70`), spills `AX → f + 0xa8`, `SI → f + 0xc8`, then `len(y) > 1` (`CMPQ DX, $1; JLE`, `DX = [f + 0x80]`)
→ the six stack-argument words `y, m` (`[f + 0x78, f + 0xa8)`) copied to `[f, f + 0x30)` and `CALL
expNNOddMontgomeryWindowSize4` (return `r4`), else the same with `expNNOddMontgomeryWindowSize2` (return `r2`); then
`ADDQ $0x68, SP; POPQ BP; RET`.

The entry layout of `expNNOdd` is window-4's (`RSP = sp + 0x388`, register arguments `z, stk, x`, stack arguments `y`
at `RSP + 8`, `m` at `RSP + 0x20`), so its entry facts are `ExpW4.EPreA` at `sp = RSP - 0x388` with window
`[sp - 8 - K, sp + 0x3f8)`. Window-4 then runs at `sp - 0x78` with `K - 0x78`, window-2 at `sp + 0xa0` with
`K + 0xa0`: both windows' windows are `[sp - 8 - K, sp + 0x380)` (`epre4` / `epre2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpOdd

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOdd"

/-- the function's names (`LibOdd`: the windows' program and `nat.expNNOdd`) -/
abbrev names : List String := LibOdd.names

/-- entry (`0x5eaf40`) -/
abbrev fnO : Nat := 6205248
/-- return address of the window-4 call (`0x5eafb7`) -/
abbrev r4 : Nat := 6205367
/-- return address of the window-2 call (`0x5eb005`) -/
abbrev r2 : Nat := 6205445

/-- the closed budget (the called window's) -/
def OBud (costF : Nat → Nat → Nat → Nat) (n costD xl ylen l b : Nat) : Prop :=
  if 1 < ylen then
    W4En.XnB costF n costD (l + StackNat.rnd (23 * n)) xl (b - stackNatCost l (23 * n)) ∧ stackNatCost l (23 * n) ≤ b
  else
    W2En.XnB costF n costD (l + StackNat.rnd (11 * n)) xl (b - stackNatCost l (11 * n)) ∧ stackNatCost l (11 * n) ≤ b

/-- the cost the postcondition charges (the called window's) -/
def OCost (n xl ylen costD l : Nat) : Nat :=
  if 1 < ylen then W4Pro.W4Cost n xl costD l else W2Pro.W2Cost n xl costD l

/-- the precondition: window-4's entry facts at `sp = RSP - 0x388` (window `[sp - 8 - K, sp + 0x3f8)`), `z`'s array
apart from the window, an empty stack array at `0`, `m` odd and `> 1`, the called window's budget -/
def PreD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) : Prop :=
  ExpW4.EPreA R b L K (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x388) st zp zc xp xl xc yp ylen mp n mc s ∧
  41632 ≤ K ∧ K + 0xa0 ≤ 2 ^ 20 ∧ Apart zp (8 * zc) ((s.regs 4).toNat - 0x388 - 8 - K) (K + 0x400) ∧
  (stCap s.mem st = 0 → stW s.mem st = 0) ∧
  st ≠ 0 ∧ natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧ OBud costF n costD xl ylen (stLen s.mem st) b

/-- the postcondition (results `RAX`, `RBX`, `RCX`), with the goroutine `g` explicit -/
@[reducible] def PostG (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD g zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  ∃ p l c : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    natVal s'.mem p l = natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n ∧ NatNorm s'.mem p l ∧
    l ≤ c ∧ (0 < c ∧ c < 2 ^ 40) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - OCost n xl ylen costD (stLen s.mem st) ≤ b' ∧
      R.inv b' L' g (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p c ∧
      ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s (K + 0x390) 0x70 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧ ResSep s.mem s'.mem st p c

/-- the postcondition: `FS` base and `DF` kept, and `PostG` -/
def PostD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K costD zp zc st xp xl yp ylen mp n : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ PostG R b L K costD (s.regs 14).toNat zp zc st xp xl yp ylen mp n s s'

/-! ### Frame transfer of the entry facts -/

theorem ap_sub {a k lo n lo' n' : Nat} (h : Apart a k lo n) (h1 : lo ≤ lo') (h2 : lo' + n' ≤ lo + n) :
    Apart a k lo' n' := by
  unfold Apart at h ⊢; omega

/-- `CEnv` on a sub-window with the same bottom -/
theorem cenv_rebase {R : RtInv} {L : List (Nat × Nat)} {g fs x K A x' K' A' : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs x K A M) (e : x' - K' = x - K) (hK' : K' ≤ x') (hA : x' + A' ≤ x + A)
    (hal : x' % 8 = 0) : CallW.CEnv R L g fs x' K' A' M := by
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨hal, hK', by omega, M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega), hg1, hg2, by omega,
    hrt.of_sub (by omega) (by omega), by unfold Apart at hga ⊢; omega, hgrt, ?_, hd, hro, f1, f2, f3, f4, f5,
    by unfold Apart at f6 ⊢; omega⟩
  intro r hr
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

theorem globals_fr {R : RtInv} {m m' : Memory} {w w' : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' w) (hw : ∀ a n, Outside a n w → Outside a n w') : RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (hgw.of_sub (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

theorem norm_fr {m m' : Memory} {w : List (Nat × Nat)} (hF : MemFrame m m' w) {p n : Nat}
    (ho : Outside p (8 * n) w) (hn : NatNorm m p n) : NatNorm m' p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · exact Or.inl h0
  rcases hn with hn | hn
  · exact Or.inl hn
  · exact Or.inr (by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn)

set_option maxRecDepth 20000 in
/-- the stack header survives a frame of the window -/
theorem hdr_fr {m m' : Memory} {lo hi st : Nat} (hF : MemFrame m m' [(lo, hi)])
    (h : Apart st 24 lo (hi - lo)) (hlo : lo ≤ hi) :
    stW m' st = stW m st ∧ stLen m' st = stLen m st ∧ stCap m' st = stCap m st := by
  unfold Apart at h
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_⟩ <;>
    (simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
theorem oe4 {R : RtInv} {L : List (Nat × Nat)} {sp K st : Nat} {m m' : Memory} {a k : Nat}
    (e0 : stW m' st = stW m st) (e1 : stLen m' st = stLen m st) (e2 : stCap m' st = stCap m st)
    (h : W4En.OE R L sp K st m a k) (hK : 0x78 ≤ K) : W4En.OE R L (sp - 0x78) (K - 0x78) st m' a k := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by unfold Apart at h2 ⊢; omega, h3, ?_⟩
  show Apart a k (stW m' st + 8 * stLen m' st) (8 * (stCap m' st - stLen m' st))
  rw [e0, e1, e2]; exact h4

set_option maxRecDepth 20000 in
theorem oe2 {R : RtInv} {L : List (Nat × Nat)} {sp K st : Nat} {m m' : Memory} {a k : Nat}
    (e0 : stW m' st = stW m st) (e1 : stLen m' st = stLen m st) (e2 : stCap m' st = stCap m st)
    (h : W4En.OE R L sp K st m a k) : W2En.OE R L (sp + 0xa0) (K + 0xa0) st m' a k := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by unfold Apart at h2 ⊢; omega, h3, ?_⟩
  show Apart a k (stW m' st + 8 * stLen m' st) (8 * (stCap m' st - stLen m' st))
  rw [e0, e1, e2]; exact h4

/-- the frame facts `epre4`/`epre2` take: the callee entry `S` after the prologue (memory framed by the window) -/
@[reducible] def AtCall (sp yp ylen mp n mc : Nat) (s S : State) : Prop :=
  S.regs 4 = BitVec.ofNat 64 (sp + 0x310) ∧ S.regs 14 = s.regs 14 ∧ S.fsBase = s.fsBase ∧ S.xmm 15 = s.xmm 15 ∧
  S.df = s.df ∧ S.mem.regions = s.mem.regions ∧
  S.mem.readLE (sp + 0x318) 8 = yp ∧ S.mem.readLE (sp + 0x320) 8 = ylen ∧ S.mem.readLE (sp + 0x330) 8 = mp ∧
  S.mem.readLE (sp + 0x338) 8 = n ∧ S.mem.readLE (sp + 0x340) 8 = mc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- window-4's entry facts at the callee entry `S` (frame `sp - 0x78`, `K - 0x78`) -/
theorem epre4 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st zp zc xp xl xc yp ylen mp n mc : Nat}
    {s S : State} (h : ExpW4.EPreA R b L K g fs sp st zp zc xp xl xc yp ylen mp n mc s) (hK : 41632 ≤ K)
    (hF : MemFrame s.mem S.mem [(sp - 8 - K, sp + 0x3f8)]) (hA : AtCall sp yp ylen mp n mc s S) :
    ExpW4.EPreA R b L (K - 0x78) g fs (sp - 0x78) st zp zc xp xl xc yp ylen mp n mc S := by
  obtain ⟨⟨-, e14, efs, ex15, edf, hal, -, hK2, hCE, hsv⟩, hgl, hty, hadx, hn, hn128, hmc0, hmc', hmO, hma, hm48,
    hmN, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxl', hxc0, hxc, hzp, hzc, hz, hgO, hsok, hstw,
    hstg, hstf, harr, hwbA, hstfr, hl16, -, -, -, -, -, hinv⟩ := h
  obtain ⟨c4, c14, cfs, cx, cdf, crg, r0, r1, r2, r3, r4⟩ := hA
  have hCE' := hCE
  obtain ⟨-, hK0, hA0, hacc, -, -, -, hrt, hga, -, -, -, -, -, -, -, -, -, hfa⟩ := hCE'
  have hsp8 : 8 ≤ sp := by omega
  obtain ⟨q0, q1, q2⟩ := hdr_fr hF (by rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hstw)
    (by omega)
  have hacc' := hF.accessible
  have ho : ∀ {a k : Nat}, Apart a k (sp - 8 - K) (K + 0x400) → Outside a k [(sp - 8 - K, sp + 0x3f8)] :=
    fun {a k} h' => by unfold Apart at h'; simp only [outside_cons, outside_nil, and_true]; omega
  have hFr : MemFrame s.mem S.mem (R.rt ++ [(sp - 8 - K, sp + 0x3f8)]) :=
    hF.mono fun a k h' => by rw [outside_append] at h'; exact h'.2
  have hCE2 := CallW.CEnv.frame hCE hFr crg (fun r hr _ => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hacc)
    (by unfold Apart at hga; simp only [outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at hfa; simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨by rw [c4]; congr 1; omega, c14.trans e14, by rw [cfs]; exact efs, cx.trans ex15, cdf.trans edf,
    by omega, by omega, by omega, cenv_rebase hCE2 (by omega) (by omega) (by omega) (by omega), hsv⟩,
    globals_fr hgl hF (fun a k h' => by simp only [outside_cons, outside_nil, and_true] at h' ⊢; omega),
    hty, by rw [hacc']; exact hadx, hn, hn128, hmc0, hmc', oe4 q0 q1 q2 hmO (by omega), by rw [hacc']; exact hma, hm48,
    norm_fr hF (ho hmO.2.1) hmN, oe4 q0 q1 q2 hyO (by omega), by rw [hacc']; exact hya, hy48,
    norm_fr hF (ho hyO.2.1) hyN, hyl, hyl', oe4 q0 q1 q2 hxO (by omega), by rw [hacc']; exact hxa, hx48,
    norm_fr hF ((ho hxO.2.1).of_sub (Nat.le_refl _) (by omega)) hxN, hxl, hxl', hxc0, hxc,
    hzp, hzc, fun hz2 => ?_, oe4 q0 q1 q2 hgO (by omega), W4Pro.stkOK_frame hsok q0 q1 q2 hF.accessible,
    ap_sub hstw (by omega) (by omega), hstg, hstf, ?_, hwbA, ?_, by rw [q1]; exact hl16,
    by rw [show sp - 0x78 + 0x390 = sp + 0x318 by omega]; exact r0,
    by rw [show sp - 0x78 + 0x398 = sp + 0x320 by omega]; exact r1,
    by rw [show sp - 0x78 + 0x3a8 = sp + 0x330 by omega]; exact r2,
    by rw [show sp - 0x78 + 0x3b0 = sp + 0x338 by omega]; exact r3,
    by rw [show sp - 0x78 + 0x3b8 = sp + 0x340 by omega]; exact r4,
    RtInv.inv_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hrt) hinv⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz hz2
    exact ⟨oe4 q0 q1 q2 a1 (by omega), by rw [hacc']; exact a2, a3, a4, a5, a6, a7, a8⟩
  · rw [q0, q2]; intro hc
    obtain ⟨a1, a2, a3⟩ := harr hc
    exact ⟨ap_sub a1 (by omega) (by omega), a2, a3⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [q0, q1, q2]; exact hstfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- window-2's entry facts at the callee entry `S` (frame `sp + 0xa0`, `K + 0xa0`) -/
theorem epre2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st zp zc xp xl xc yp ylen mp n mc : Nat}
    {s S : State} (h : ExpW4.EPreA R b L K g fs sp st zp zc xp xl xc yp ylen mp n mc s) (hK : 41632 ≤ K) (hK2 : K + 0xa0 ≤ 2 ^ 20)
    (hF : MemFrame s.mem S.mem [(sp - 8 - K, sp + 0x3f8)]) (hA : AtCall sp yp ylen mp n mc s S) :
    ExpW2.EPreA R b L (K + 0xa0) g fs (sp + 0xa0) st zp zc xp xl xc yp ylen mp n mc S := by
  obtain ⟨⟨-, e14, efs, ex15, edf, hal, -, -, hCE, hsv⟩, hgl, hty, hadx, hn, hn128, hmc0, hmc', hmO, hma, hm48,
    hmN, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxl', hxc0, hxc, hzp, hzc, hz, hgO, hsok, hstw,
    hstg, hstf, harr, hwbA, hstfr, hl16, -, -, -, -, -, hinv⟩ := h
  obtain ⟨c4, c14, cfs, cx, cdf, crg, r0, r1, r2, r3, r4⟩ := hA
  have hCE' := hCE
  obtain ⟨-, hK0, hA0, hacc, -, -, -, hrt, hga, -, -, -, -, -, -, -, -, -, hfa⟩ := hCE'
  have hsp8 : 8 ≤ sp := by omega
  obtain ⟨q0, q1, q2⟩ := hdr_fr hF (by rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hstw)
    (by omega)
  have hacc' := hF.accessible
  have ho : ∀ {a k : Nat}, Apart a k (sp - 8 - K) (K + 0x400) → Outside a k [(sp - 8 - K, sp + 0x3f8)] :=
    fun {a k} h' => by unfold Apart at h'; simp only [outside_cons, outside_nil, and_true]; omega
  have hFr : MemFrame s.mem S.mem (R.rt ++ [(sp - 8 - K, sp + 0x3f8)]) :=
    hF.mono fun a k h' => by rw [outside_append] at h'; exact h'.2
  have hCE2 := CallW.CEnv.frame hCE hFr crg (fun r hr _ => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hacc)
    (by unfold Apart at hga; simp only [outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at hfa; simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨by rw [c4], c14.trans e14, by rw [cfs]; exact efs, cx.trans ex15, cdf.trans edf,
    by omega, by omega, by omega, cenv_rebase hCE2 (by omega) (by omega) (by omega) (by omega), hsv⟩,
    globals_fr hgl hF (fun a k h' => by simp only [outside_cons, outside_nil, and_true] at h' ⊢; omega),
    hty, by rw [hacc']; exact hadx, hn, hn128, hmc0, hmc', oe2 q0 q1 q2 hmO, by rw [hacc']; exact hma, hm48,
    norm_fr hF (ho hmO.2.1) hmN, oe2 q0 q1 q2 hyO, by rw [hacc']; exact hya, hy48,
    norm_fr hF (ho hyO.2.1) hyN, hyl, hyl', oe2 q0 q1 q2 hxO, by rw [hacc']; exact hxa, hx48,
    norm_fr hF ((ho hxO.2.1).of_sub (Nat.le_refl _) (by omega)) hxN, hxl, hxl', hxc0, hxc,
    hzp, hzc, fun hz2 => ?_, oe2 q0 q1 q2 hgO, W4Pro.stkOK_frame hsok q0 q1 q2 hF.accessible,
    ap_sub hstw (by omega) (by omega), hstg, hstf, ?_, hwbA, ?_, by rw [q1]; omega,
    by rw [show sp + 0xa0 + 0x278 = sp + 0x318 by omega]; exact r0,
    by rw [show sp + 0xa0 + 0x280 = sp + 0x320 by omega]; exact r1,
    by rw [show sp + 0xa0 + 0x290 = sp + 0x330 by omega]; exact r2,
    by rw [show sp + 0xa0 + 0x298 = sp + 0x338 by omega]; exact r3,
    by rw [show sp + 0xa0 + 0x2a0 = sp + 0x340 by omega]; exact r4,
    RtInv.inv_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 0x3f8 - (sp - 8 - K) = K + 0x400 by omega]; exact hrt) hinv⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz hz2
    exact ⟨oe2 q0 q1 q2 a1, by rw [hacc']; exact a2, a3, a4, a5, a6, a7, a8⟩
  · rw [q0, q2]; intro hc
    obtain ⟨a1, a2, a3⟩ := harr hc
    exact ⟨ap_sub a1 (by omega) (by omega), a2, a3⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [q0, q1, q2]; exact hstfr


end FvModexp.Amd64.ExpOdd
