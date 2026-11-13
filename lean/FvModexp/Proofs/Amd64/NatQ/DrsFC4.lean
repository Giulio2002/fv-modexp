import FvModexp.Proofs.Amd64.NatQ.DrsFC4R
import FvModexp.Proofs.Amd64.NatQ.DrsC4

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC4.lean; adapted from Amd64/NatQ/DrsC4.lean)
# `divRecursiveStep` (amd64), final correction loop: `c := subVV(qhatv[:s], qhatv[:s], v[:s])` (natdiv.go:873)

`c4F`: from the `subVV.abi0` entry `X` (`RSP = r - 400`, return `0x5f0457`) → `subVV.abi0` (`svvD`) → the re-entry
sequence (`XORPS X15, X15`; `MOVQ FS:-8, R14`) → `0x5f0464` with `BxF … stb (stV V s st)` and the carry at `r - 320`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)
open FvModexp.Amd64.Callees (VVLPre SubVVLQ SubVVHyp subVVHyp)

/-- the pc after the re-entry sequence of the final loop's `subVV.abi0` call -/
abbrev rFV2 : Nat := 0x5f0464

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `McF` across the argument stores (`isA`) -/
theorem McF.ownA {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : McF R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (isA s))
    (hreg : M'.regions = M.regions) : McF R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, isA, outside_cons, outside_nil, and_true]; omega)
      (by simp only [FOut, isA, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s200⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.wk, bud_cap (Cr.capOwn hcr hF) h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`c := subVV(qhatv[:s], qhatv[:s], v[:s])`** (final loop) from its callee entry, through the re-entry sequence -/
theorem c4F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb st : Mdl.St) (Q : State → Prop) (T : State) (hbx : BxF R c s Lk bk T j Z U qv i stb st)
    (X : State) (hpc : X.rip = BitVec.ofNat 64 subVVA) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false)
    (hF : MemFrame T.mem X.mem (isA s)) (hreg : X.mem.regions = T.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFV1)
    (ez : X.mem.readLE ((s.regs 4).toNat - 392) 8 = qv) (en : X.mem.readLE ((s.regs 4).toNat - 384) 8 = c.vl / 2 - 1)
    (ex : X.mem.readLE ((s.regs 4).toNat - 368) 8 = qv) (ey : X.mem.readLE ((s.regs 4).toNat - 344) 8 = c.vp)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rFV2 →
      BxF R c s Lk bk T' j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) st) →
      T'.mem.readLE ((s.regs 4).toNat - 320) 8 =
        (Mdl.subVV (st.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hmc0 := hbx.mc
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, hga, -, -, -, ⟨-, -, htg⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨hva, hv48, -, -, -, -, -⟩ := hpre.va
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul; have h40 := hcr.h40
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hmc := McF.ownA hmc0 hF hreg
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : CallEnv R Lk X 0 88 := Ev.callEnv hcr hmc.ev hspn h14 hfs (by omega) (by omega)
  obtain ⟨-, -, -, -, -, -, -, hLs, -, ⟨htlX, -, -⟩⟩ := hce'
  have hfa : (18446744073709551608 + X.fsBase.toNat) % 18446744073709551616 = X.fsBase.toNat - 8 := by
    have := htlX.base; omega
  have hfrd := htlX.readable
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have hrg := hmc.rg
  have hqa := hmc.qa
  have hq48 := Janus.Arm64.Memory.accessible_bound _ hqa
  have hrw := hrg.w
  simp only [win, outside_cons, outside_nil, and_true] at hrw huw
  have hs3 : c.vl / 2 - 1 ≤ 3 * c.vl := by omega
  -- the frame words, at `RSP`
  have ez' : X.mem.readLE ((X.regs 4).toNat + 8) 8 = qv := by rw [hspn, show (s.regs 4).toNat - 400 + 8 = (s.regs 4).toNat - 392 by omega]; exact ez
  have en' : X.mem.readLE ((X.regs 4).toNat + 16) 8 = c.vl / 2 - 1 := by rw [hspn, show (s.regs 4).toNat - 400 + 16 = (s.regs 4).toNat - 384 by omega]; exact en
  have ex' : X.mem.readLE ((X.regs 4).toNat + 32) 8 = qv := by rw [hspn, show (s.regs 4).toNat - 400 + 32 = (s.regs 4).toNat - 368 by omega]; exact ex
  have ey' : X.mem.readLE ((X.regs 4).toNat + 56) 8 = c.vp := by rw [hspn, show (s.regs 4).toNat - 400 + 56 = (s.regs 4).toNat - 344 by omega]; exact ey
  have e80 : (X.regs 4).toNat + 80 = (s.regs 4).toNat - 320 := by omega
  have hXacc : ∀ a n v, X.mem.accessible a n v = s.mem.accessible a n v := fun a n v => by
    rw [hF.accessible, hmc0.ev.fr.accessible]
  have hpreV : VVLPre R bk Lk X := by
    unfold VVLPre Callees.VVPre
    rw [ez', en', ex', ey']
    refine ⟨⟨ez', en', ex', ey', by rw [hspn, hra]; decide, by omega,
        by rw [hXacc, hspn]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega),
        Janus.Arm64.Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega),
        Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hqa (Nat.le_refl _) (by omega)),
        by rw [hXacc]; exact Janus.Arm64.Memory.accessible_mono _ hva (Nat.le_refl _) (by omega), Or.inl rfl,
        Or.inr ?_, ?_⟩, by rw [h14]; exact hmc.ev.inv, hrg.h.sub (Nat.le_refl _) (by omega),
      hout.of_sub (by omega) (by omega), ?_, ?_, ?_, ?_⟩
    · have := hrg.v; unfold Apart at this ⊢; omega
    · unfold Apart; omega
    · have := hrg.g; rw [h14]; unfold Apart at this ⊢; simp only [grd] at this; omega
    · rw [h14]; unfold Apart at hga ⊢; omega
    · have := hrg.fs; rw [hfs]; unfold Apart at this ⊢; simp only [tls] at this; omega
    · have htw := hpre.ce.2.2.2.2.2.2.2.2.2.2.2; rw [hfs]; unfold Apart at htw ⊢; omega
  refine ReachesRet.call_regions (svvD impl hap R bk Lk) hpc hpreV fun T' hT hq hrgT => ?_
  obtain ⟨junk, f, v, vh, mx, m, z, rfl, -, ⟨hval, hcar, hfr⟩, hinv, -, htls⟩ := hq
  simp only [ez', en', ex', ey', e80] at hval hcar hfr
  rw [h14] at hinv
  have hregm : m.regions = X.mem.regions := hrgT
  have hcar1 : m.readLE ((s.regs 4).toNat - 320) 8 ≤ 1 := by rw [hcar]; split <;> omega
  -- the buffer after the call
  obtain ⟨hz1, hb1⟩ := Asm.subVV_model X.mem m qv qv c.vp (c.vl / 2 - 1) _ hcar1 hval
  have hV : Asm.limbs X.mem c.vp (c.vl / 2 - 1) = (c.V s).take (c.vl / 2 - 1) := by
    rw [← Asm.limbs_take X.mem c.vp c.vl _ (by omega), limbs_congr hmc.bd.vk]
  have hB : Asm.limbs X.mem qv (c.vl / 2 - 1) = st.buf.take (c.vl / 2 - 1) := by
    rw [← hmc.bf, Asm.limbs_take _ _ _ _ hs3]
  have hbf : Asm.limbs m qv (3 * c.vl) = (stV (c.V s) (c.vl / 2 - 1) st).buf := by
    rw [Asm.limbs_upd (m := X.mem) (j := 0) (k := c.vl / 2 - 1) (by omega) (fun i hi hi2 => hfr.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)), Mdl.upd_zero, hmc.bf]
    simp only [Nat.mul_zero, Nat.add_zero, Asm.length_limbs]
    rw [hz1, hB, hV]
  -- the frame of the call in the `McF.callN` form
  have hF' : MemFrame X.mem m (R.rt ++ win X 0 88 ++ [(qv, qv + 8 * (c.vl / 2 - 1))]) := hfr.mono fun x n ho => by
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    rw [hspn] at ho; omega
  have hL' : LiveFrame X.mem m Lk [(qv, qv + 8 * (c.vl / 2 - 1))] := ⟨fun x n hin ho => hfr.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ho ⊢
    rw [hspn] at this; omega)⟩
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Outside x n [(qv, qv + 8 * (c.vl / 2 - 1))] →
      m.readLE x n = X.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hF' hL' hh hw' ho
  have hloc := hmc.qloc.out
  have hsub : ∀ x n, Outside x n [(qv, qv + 8 * (3 * c.vl))] → Outside x n [(qv, qv + 8 * (c.vl / 2 - 1))] :=
    fun x n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have ap : ∀ {x n}, Apart qv (8 * (3 * c.vl)) x n → Apart x n qv (8 * (c.vl / 2 - 1)) := fun h => by
    unfold Apart at h ⊢; omega
  have ht0 := hrg.t0
  have hu := hrg.u
  have kT : m.readLE c.t0 (8 * (c.qF s U).length) = X.mem.readLE c.t0 (8 * (c.qF s U).length) := by
    have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
    refine rk _ _ ((hmc.ev.ext.held hcr.t0h).sub (Nat.le_refl _) (by omega)) (hcr.t0w.of_sub (Nat.le_refl _) (by omega)) ?_
    unfold Apart at ht0; simp only [outside_cons, outside_nil, and_true]; omega
  have kW : m.readLE c.up (8 * c.u1) = X.mem.readLE c.up (8 * c.u1) :=
    rk _ _ (hext.held (huh.sub (by omega) (by omega))) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart at hu; simp only [outside_cons, outside_nil, and_true]; omega)
  have hmcT : McF R c s Lk bk m j Z U qv (stV (c.V s) (c.vl / 2 - 1) st) :=
    McF.callN hmc hspn (by omega) (by omega) hF' hL' (LiveExt.refl R Lk) hinv hregm (Nat.le_refl _)
      (fun x n h => hsub _ _ (hloc.1 x n h)) (fun x n h1 h2 => hsub _ _ (hloc.2 x n h1 h2))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by have := hrg.st; unfold Apart at this ⊢; omega) (ap hrg.v)
      (ap (apR hrg.u (by omega) (by omega))) (ap hrg.q)
      (by rw [limbs_congr kT]; exact hmc.qk) hbf (by rw [limbs_congr kW]; exact hmc.wk)
  -- the slots
  have o : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 320 ∨ (s.regs 4).toNat - 312 ≤ a) → (s.regs 4).toNat - 408 ≤ a →
      a + 8 ≤ (s.regs 4).toNat + 96 → m.readLE a 8 = X.mem.readLE a 8 := fun a h1 h2 h3 => hfr.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]; omega)
  have hv4 := hbx.v3
  have hv4m : V3F c s m qv (c.PF s U).length :=
    ⟨(by rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact hv4.s320),
      (by rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact hv4.s144),
      (by rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact hv4.s160)⟩
  have hsim : m.readLE ((s.regs 4).toNat - 184) 8 = i := by
    rw [o _ (by omega) (by omega) (by omega), hF.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]
    exact hbx.si
  have hcm : m.readLE ((s.regs 4).toNat - 320) 8 =
      (Mdl.subVV (st.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 := by
    rw [← hB, ← hV]; exact hb1
  -- the re-entry sequence: `XORPS X15, X15; MOVQ FS:-8, R14`
  have htg' : m.readLE (X.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [htls, hfs]
    have e := Ev.tls hcr hmc.ev
    simp only [tls] at e
    rw [e]; simp only [regG] at htg; exact htg
  have hfrm : m.accessible (X.fsBase.toNat - 8) 8 false = true := by rw [hfr.accessible]; exact hfrd
  have hraX : X.mem.readLE (X.regs 4).toNat 8 = rFV1 := by rw [hspn]; exact hra
  have hB1 : Box (McF R c s Lk bk m j Z U qv (stV (c.V s) (c.vl / 2 - 1) st)) := ⟨hmcT⟩
  have hB2 : Box (V3F c s m qv (c.PF s U).length) := ⟨hv4m⟩
  have hbi := hbx.hi; have hbp := hbx.pos; have hbv := hbx.inv
  clear hmcT hv4m hmc hmc0 hbx hF' hL' rk kT kW hval hcar hfr hinv
  janus64_run [hraX, htg', hfa, hfrm] until [rFV2]
  refine k _ rfl ⟨?sp, ?r5, ?r14, ?fs, ?df, ?x15, hB1.h, hB2.h, hsim, hbi, hbp, hbv⟩ hcm
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, regs0, Nat.reduceEqDiff, ↓reduceIte, regSP]; rw [hsp]; bv_omega
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, regs0, Nat.reduceEqDiff, ↓reduceIte, regSP, regFP]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case fs => exact hfs
  case df => dsimp only
  case x15 => simp only [Janus.Amd64.Tactic.setXmmF_apply, ↓reduceIte]

end FvModexp.Amd64.Q.DivRec
