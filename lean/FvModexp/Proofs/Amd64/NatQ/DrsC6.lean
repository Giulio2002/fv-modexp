import FvModexp.Proofs.Amd64.NatQ.DrsC5R
import FvModexp.Proofs.Amd64.Nat.AddTo

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsC6.lean)
# `divRecursiveStep` (amd64), correction loop: `addTo(uu[s:], v[s:])` (natdiv.go:842)

`c6`: from the `CALL addTo` entry `X` (`RSP = r - 400`, return `0x5efd85`; `Bx … stb (stC …)` at the pre-call state
`T`) → `addTo` (`AddTo.ens` on `LibDrs`; window `win X 4232 48`; writes `u[j-1 : u1]`) → its return `0x5efd85` with
`Bx … stb (corrOnce V s ql stb)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

theorem addTo_entryD : segAddr Extracted.program AddTo.fn = addToC := by decide

/-- `addTo` as a summary in `LibDrs.program` -/
theorem atSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibDrs.program.link impl) addToC
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [zp, zl, zc, xp, xl, xc] ∧ s.df = false ∧
        (CallEnv R L s 4232 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4232 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4232 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 14).toNat + 16) 8 ∧ Apart zp.toNat (8 * zl.toNat) (s.fsBase.toNat - 8) 8 ∧
          R.inv b L (s.regs 14).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        (s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ win s 4232 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have hS := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc)
    (A64.noExit_restrict64 hap AddTo.names) (by simp [numIntRegs])
    (A64.codeIn_restrict_mono64 hap (IntAS.sub_of_all (ms := LibDrs.names) (by decide)))
  rw [← LibDrs.eq_only, addTo_entryD] at hS
  exact hS

set_option maxRecDepth 20000 in
/-- the return site `0x5efd85` is admissible for `addTo`'s program -/
theorem raA (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) rA := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := AddTo.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0x505 (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

theorem ws_up0 {c : Cx} {s : State} {x k p n : Nat} (h : Outside x k (c.ws s)) (h1 : c.up ≤ p)
    (h2 : p + n ≤ c.up + 8 * c.ul) : Outside x k [(p, p + n)] := by
  simp only [Cx.ws, outside_append, outside_cons] at h
  simp only [outside_cons, outside_nil, and_true]; omega

theorem ws_up {c : Cx} {s : State} {rs : List (Nat × Nat)} {x k p n : Nat} (h : Outside x k (rs ++ c.ws s))
    (h1 : c.up ≤ p) (h2 : p + n ≤ c.up + 8 * c.ul) : Outside x k [(p, p + n)] :=
  ws_up0 ((outside_append _ _ _ _).mp h).2 h1 h2

theorem limbs_eq2 {m : Memory} {a a' n n' : Nat} (h1 : a = a') (h2 : n = n') : Asm.limbs m a n = Asm.limbs m a' n' := by
  subst h1; subst h2; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`addTo(uu[s:], v[s:])`** from its callee entry -/
theorem c6 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop) (T : State)
    (hby : Bx R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb))
    (X : State) (hpc : X.rip = BitVec.ofNat 64 addToC) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1))) (h3 : X.regs 3 = BitVec.ofNat 64 (c.u1 - j + 1))
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.uc - (j - 1))) (h7 : X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)))
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1)) (h8 : X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)))
    (hFR : MemFrame T.mem X.mem (isR s)) (hreg0 : X.mem.regions = T.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rA)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rA → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      Bx R c s L' b' T' j Z U qv i stb (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hmc0 := hby.mc
  have hcr := hmc0.cr
  have hpre := hcr.pre
  have hup8 : c.up % 8 = 0 := hpre.stl.2.2.2.2.1
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hua, hu48, huh, huw, hug⟩ := hpre.ua
  obtain ⟨hva, hv48, hvh, hvw, -, -, -⟩ := hpre.va
  have hv9 := hpre.v9.1; have hvc40 := hpre.vc40; have hvlc := hpre.vlc
  have hul := hpre.ulc; have huc := hpre.uc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by have := hmc0.li.2.2.2.2.2.2.2; omega
  have hjB := hmc0.jB
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF1 : MemFrame T.mem X.mem (is1 s) := hFR.mono fun x n ho => by
    simp only [isR, is1, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := Mc.own1 hmc0 hF1 hreg0
  have hv4X := V4.own1 hby.v4 hF1 h0'
  have hsiX : X.mem.readLE ((s.regs 4).toNat - 176) 8 = i := by
    rw [hFR.readLE _ _ (by simp only [isR, outside_cons, outside_nil, and_true]; omega)]; exact hby.si
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 4232 48 := Ev.callEnv hcr hmc.ev hspn h14 hfs (by omega) (by omega)
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hmc.ev.fr.accessible]
  simp only [win, outside_cons, outside_nil, and_true] at huw hvw
  have hqu := hpre.qu; have huv := hpre.uv; have hus := hpre.su.1; have hutl := hpre.tl.2.1
  have t0 := tN (by omega : c.up + 8 * (j - 1) < 2 ^ 64)
  have t1 := tN (by omega : c.u1 - j + 1 < 2 ^ 64)
  have t2 := tN (by omega : c.uc - (j - 1) < 2 ^ 64)
  have t3 := tN (by omega : c.vp + 8 * (c.vl / 2 - 1) < 2 ^ 64)
  have t4 := tN (by omega : c.vl - c.vl / 2 + 1 < 2 ^ 64)
  have t5 := tN (by omega : c.vc - (c.vl / 2 - 1) < 2 ^ 64)
  refine ReachesRet.call_regions (atSum impl hap R hmv bk Lk (X.regs 0) (X.regs 3) (X.regs 1) (X.regs 7)
    (X.regs 6) (X.regs 8)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, ⟨g1, g2, hq⟩⟩ hrgT => ?_)
  case ra => rw [show (X.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raA impl hap
  case pre =>
    rw [h0, h3, h1, h7, h6, t0, t1, t2, t3, t4]
    refine ⟨hce', by omega, by omega, by omega, fun _ => ⟨by omega, hext.held (huh.sub (by omega) (by omega)),
      by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega), by omega⟩, ?_, by omega,
      by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hva (by omega) (by omega), by omega,
      hext.held (hvh.sub (by omega) (by omega)), ?_, fun _ => ?_, ?_, ?_, by rw [h14]; exact hmc.ev.inv⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · unfold Apart at huv ⊢; omega
    · rw [h14]; unfold Apart at hug ⊢; omega
    · rw [hfs]; unfold Apart at hutl ⊢; omega
  rw [h0, h3, h7, h6, t0, t1, t3, t4] at hq
  obtain ⟨hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = X.mem.regions := hrgT
  rw [h14] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) →
      Outside x n [(c.up + 8 * (j - 1), c.up + 8 * (j - 1) + 8 * (c.u1 - j + 1))] →
      T'.mem.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Janus.Arm64.Memory.accessible_bound _ hqa
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  have t0u := hcr.t0u
  have kT : T'.mem.readLE c.t0 (8 * (c.q0 s j U).length) = X.mem.readLE c.t0 (8 * (c.q0 s j U).length) := by
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega
  have kQ : T'.mem.readLE qv (8 * (3 * c.vl)) = X.mem.readLE qv (8 * (3 * c.vl)) := by
    refine rk _ _ hrg.h hrg.w ?_
    have := hrg.u; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  -- the remainder window `uu = u[j-B:u1]` after the call
  have hzv : Asm.limbs T'.mem (c.up + 8 * (j - 1)) (c.u1 - j + 1) =
      Mdl.addTo (Asm.limbs X.mem (c.up + 8 * (j - 1)) (c.u1 - j + 1))
        (Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1)) :=
    Asm.addTo_model X.mem T'.mem _ _ _ _ (by omega) hval
  have hwX : Asm.limbs X.mem (c.up + 8 * (j - 1)) (c.u1 - j + 1) =
      (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb).w.drop (c.vl / 2 - 1) := by
    rw [← hmc.wk, Asm.limbs_drop]
    exact limbs_eq2 (by omega) (by omega)
  have hvX : Asm.limbs X.mem (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) = (c.V s).drop (c.vl / 2 - 1) := by
    show _ = (Asm.limbs s.mem c.vp c.vl).drop _
    rw [Asm.limbs_drop, show c.vl - (c.vl / 2 - 1) = c.vl - c.vl / 2 + 1 by omega]
    exact limbs_congr (rd_sub hmc.bd.vk (by omega) (by omega))
  have hwk : Asm.limbs T'.mem (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) =
      (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb).w := by
    rw [Asm.limbs_upd (m := X.mem) (j := c.vl / 2 - 1) (k := c.u1 - j + 1) (by omega)
      (fun i hi hi2 => rk _ _ (hext.held (huh.sub (by omega) (by omega))) (by
        simp only [win, outside_cons, outside_nil, and_true]; omega)
        (by simp only [outside_cons, outside_nil, and_true]; omega)), hmc.wk]
    rw [show c.up + 8 * (j - c.vl / 2) + 8 * (c.vl / 2 - 1) = c.up + 8 * (j - 1) by omega, hzv, hwX, hvX]
    rfl
  have hpn : c.up + 8 * (j - 1) + 8 * (c.u1 - j + 1) ≤ c.up + 8 * c.ul := by omega
  have hmcT : Mc R c s L' b' T'.mem j Z U qv (Mdl.corrOnce (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) :=
    Mc.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun _ _ h => ws_up h (Nat.le_add_right _ _) hpn) (fun _ _ _ h => ws_up0 h (Nat.le_add_right _ _) hpn)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hus ⊢; omega) (by unfold Apart at huv ⊢; omega) (by unfold Apart; omega)
      (by unfold Apart at hqu ⊢; omega) (by unfold Apart; omega)
      (by rw [limbs_congr kT]; exact hmc.qk) (by rw [limbs_congr kQ]; exact hmc.bf) hwk
  have hhi : HiOut s (R.rt ++ win X 4232 48 ++ [(c.up + 8 * (j - 1), c.up + 8 * (j - 1) + 8 * (c.u1 - j + 1))]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T' (by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]) L' b'
    ⟨by rw [f1, hsp]; bv_omega, f2.trans h5, f3.trans h14, g1.trans hfs, g2.trans hdf, f4.trans hx15, hmcT,
      hv4X.frame hMF hhi h0', ?_, hby.hi, hby.pos, hby.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hsiX

end FvModexp.Amd64.Q.DivRec
