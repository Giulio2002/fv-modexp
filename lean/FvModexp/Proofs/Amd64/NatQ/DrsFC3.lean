import FvModexp.Proofs.Amd64.NatQ.DrsFC2B
import FvModexp.Proofs.Amd64.NatQ.DrsC3

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC3.lean; adapted from Amd64/NatQ/DrsC3.lean)
# `divRecursiveStep` (amd64), final correction loop: `subVW(qhat, qhat, 1)` (natdiv.go:872)

`c3F`: from the `CALL subVW` entry `Y` (`RSP = r - 400`, return `0x5f03f5`; `BxF … stb stb` at the pre-call state `T`)
→ `subVW` (`vwSum`, in place; window `win Y 4136 40`) → its return with `BxF … stb (stQ stb)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
/-- the return site `0x5f03f5` (after `CALL subVW(qhat, qhat, 1)`) is admissible for `subVW`'s program -/
theorem raWF1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments [SubVW.fn]).link impl) rFW1 := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := [SubVW.fn])
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; decide) 0xb75 (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`subVW(qhat, qhat, 1)`** from its callee entry -/
theorem c3F (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (j : Nat) (Z U : List Nat) (qv i : Nat)
    (stb : Mdl.St) (Q : State → Prop) (T : State) (hbx : BxF R c s Lk bk T j Z U qv i stb stb)
    (Y : State) (hpc : Y.rip = BitVec.ofNat 64 SubVW.entry) (hsp : Y.regs 4 = s.regs 4 - 400#64)
    (h5 : Y.regs 5 = s.regs 4 - 8#64) (h14 : Y.regs 14 = s.regs 14) (hfs : Y.fsBase = s.fsBase)
    (hdf : Y.df = false) (hx15 : Y.xmm 15 = 0#128)
    (h0 : Y.regs 0 = BitVec.ofNat 64 c.t0) (h3 : Y.regs 3 = BitVec.ofNat 64 (c.qF s U).length)
    (h1 : Y.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h7 : Y.regs 7 = BitVec.ofNat 64 c.t0)
    (h6 : Y.regs 6 = BitVec.ofNat 64 (c.qF s U).length) (h8 : Y.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h9 : Y.regs 9 = 1#64) (hFR : MemFrame T.mem Y.mem (isR s)) (hreg0 : Y.mem.regions = T.mem.regions)
    (hra : Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rFW1)
    (k : ∀ T' : State, T'.rip = BitVec.ofNat 64 rFW1 → ∀ (L' : List (Nat × Nat)) (b' : Nat),
      BxF R c s L' b' T' j Z U qv i stb (stQ stb) → ReachesRet (LibDrs.program.link impl) (retAddrOf s) T' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q := by
  have hmc0 := hbx.mc
  have hcr := hmc0.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  -- `McF` at `Y` (the return-slot store `isR` is inside `is1F`)
  have hF1 : MemFrame T.mem Y.mem (is1F s) := hFR.mono fun x n ho => by
    simp only [isR, is1F, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hmc := McF.own1 hmc0 hF1 hreg0
  have hv4Y := V3F.own1 hbx.v3 hF1 h0'
  have hsiY : Y.mem.readLE ((s.regs 4).toNat - 184) 8 = i := by
    rw [hFR.readLE _ _ (by simp only [isR, outside_cons, outside_nil, and_true]; omega)]; exact hbx.si
  have hspn : (Y.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hce' : Callees.CallEnvND R Lk Y 4136 40 := by
    obtain ⟨g1, g2, g3, -, g5, g6, g7, g8, -, g10, g11, g12⟩ :=
      Ev.callEnv (k := 4136) (a := 40) hcr hmc.ev hspn h14 hfs (by omega) (by omega)
    exact ⟨g1, g2, g3, g5, g6, g7, g8, g10, g11, g12⟩
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hmc.ev.ext
  have ht0w := hcr.t0w
  have ht0g := hcr.t0g
  have ht0f := hcr.t0fs
  have ht0al := hcr.t0al; have ht048 := hcr.t048
  have ht0acc : Y.mem.accessible c.t0 (8 * (c.vl / 2 + 1)) true = true := by
    rw [hmc.ev.fr.accessible]; exact hcr.t0acc
  have ht0h : Held R Lk c.t0 (8 * (c.vl / 2 + 1)) := hmc.ev.ext.held hcr.t0h
  simp only [win, outside_cons, outside_nil, and_true] at ht0w
  have t0 := tN (by omega : c.t0 < 2 ^ 64)
  have t1 := tN (by omega : (c.qF s U).length < 2 ^ 64)
  have t2 := tN (by omega : c.vl / 2 + 1 < 2 ^ 64)
  refine ReachesRet.call_regions (vwSum impl hap R hmv bk Lk (Y.regs 0) (Y.regs 3) (Y.regs 1) (Y.regs 7)
    (Y.regs 6) (Y.regs 8) (Y.regs 9)) hpc
    ⟨?ra, hx15, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hdf, ?xz, ?pre⟩
    (fun T' hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra => rw [show (Y.regs regSP).toNat = (s.regs 4).toNat - 400 from hspn, hra]; exact raWF1 impl hap
  case xz => rw [h6, h3]
  case pre =>
    have e03 : Y.regs 0 = Y.regs 7 := by rw [h0, h7]
    unfold SubVW.Pre
    rw [if_pos e03]
    rw [h0, h3, h1, h7, h8, t0, t1, t2]
    refine ⟨hce', hql, hql, by omega, by omega, fun _ => ⟨ht0al, ht0h.sub (Nat.le_refl _) (by omega),
      Janus.Arm64.Memory.accessible_mono _ ht0acc (Nat.le_refl _) (by omega), by omega⟩, ?_, ?_, ?_, by omega,
      ht0h.sub (Nat.le_refl _) (by omega), ?_, Or.inl rfl, by rw [h14]; exact hmc.ev.inv, trivial⟩
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
    · intro _; rw [h14, hfs]; unfold Apart at ht0g ht0f ⊢; simp only [grd, tls] at ht0g ht0f; omega
    · exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ ht0acc (Nat.le_refl _) (by omega))
    · simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  unfold SubVW.Post at hq
  rw [h0, h3, h7, h9, t0, t1] at hq
  obtain ⟨g1, g2, -, hval, L', b', hx, hb, hinv, hMF, hLF⟩ := hq
  have hreg : T'.mem.regions = Y.mem.regions := hrg
  rw [h14] at hinv
  -- the reads kept by the call
  have rk : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Outside x n [(c.t0, c.t0 + 8 * (c.qF s U).length)] →
      T'.mem.readLE x n = Y.mem.readLE x n := fun x n hh hw' ho => keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ho
  have hrg' := hmc.rg
  have kQ : T'.mem.readLE qv (8 * (3 * c.vl)) = Y.mem.readLE qv (8 * (3 * c.vl)) :=
    rk _ _ hrg'.h hrg'.w (by
      have := hrg'.t0; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega)
  have t0u := hcr.t0u
  have kW : T'.mem.readLE c.up (8 * c.u1) = Y.mem.readLE c.up (8 * c.u1) :=
    rk _ _ (hext.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega)) (by
      unfold Apart at t0u; simp only [outside_cons, outside_nil, and_true]; omega)
  -- the new `qhat`
  have hqk : Asm.limbs T'.mem c.t0 (c.qF s U).length = (stQ stb).qhat := by
    have := (Asm.subVW_model Y.mem T'.mem c.t0 c.t0 (c.qF s U).length 1 _ (by decide) hval rfl).1
    rw [this, hmc.qk]
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hsub : ∀ x n, Outside x n [(c.t0, c.t0 + 8 * (c.vl / 2 + 1))] →
      Outside x n [(c.t0, c.t0 + 8 * (c.qF s U).length)] := fun x n h => by
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have ap : ∀ {x n}, Apart c.t0 (8 * (c.vl / 2 + 1)) x n → Apart x n c.t0 (8 * (c.qF s U).length) := fun h => by
    unfold Apart at h ⊢; omega
  have hmcT : McF R c s L' b' T'.mem j Z U qv (stQ stb) :=
    McF.callN hmc hspn (by omega) (by omega) hMF hLF hx hinv hreg hb
      (fun x n h => hsub _ _ (hloc.1 x n h)) (fun x n h1 h2 => hsub _ _ (hloc.2 x n h1 h2))
      (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by have := hcr.t0st; unfold Apart at this ⊢; omega) (ap hcr.t0v)
      (ap (apR hcr.t0u (by omega) (by omega))) (ap hcr.t0q)
      hqk (by rw [limbs_congr kQ]; exact hmc.bf) (by rw [limbs_congr kW]; exact hmc.wk)
  have hhi : HiOut s (R.rt ++ win Y 4136 40 ++ [(c.t0, c.t0 + 8 * (c.qF s U).length)]) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hiOut_win (W := c.W)
      (by simp only [win, outside_cons, outside_nil, and_true]; omega) (by omega) (by omega))
  refine k T' (by rw [hT]; simp only [retAddrOf]; rw [hspn, hra]) L' b'
    ⟨by rw [f1, hsp]; bv_omega, f2.trans h5, f3.trans h14, g1.trans hfs, g2.trans hdf, f4.trans hx15, hmcT,
      hv4Y.frame hMF hhi h0', ?_, hbx.hi, hbx.pos, hbx.inv⟩
  rw [hMF.readLE _ _ (hhi.of_sub (by omega) (by omega))]; exact hsiY

end FvModexp.Amd64.Q.DivRec
