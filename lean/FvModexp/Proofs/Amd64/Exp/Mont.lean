import FvModexp.Proofs.Amd64.Exp.MontLoop
import FvModexp.Proofs.Amd64.Exp.MontAsm

/-!
# `nat.montgomery` (amd64), nat.go:188-218: the roomy summary (see the arm64 twin for the statement's meaning)

ABIInternal on amd64 passes 9 integer arguments in registers: `z`, `x`, `y` in `RAX…R11`; `m`, `k`, `n` are on the
caller's stack at `RSP+8 … RSP+40` (the precondition names their words). Frame: `PUSHQ BP; SUBQ $0xb0, SP`;
the runtime calls need 4096 bytes below the pushed return address: `stk = 0xb8 + 8 + 4096 = 4288`; the function writes
its caller's spill area up to `RSP + 0x68` (`above = 104`, including the return-address slot).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.MontHyp FvModexp.Exp

namespace FvModexp.Amd64.Mont

/-- the call environment (agent top's amd64 `CallEnv` without `DataLoaded`), plus the amd64 ABIInternal register
invariants `X15 = 0`, `DF = 0` and the TLS `g` slot the ABI0 re-entries read -/
@[reducible] def Env (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  StackGuardOK s stk ∧ StackWritable s stk above ∧ (s.regs 4).toNat % 8 = 0 ∧
    Outside ((s.regs 4).toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - stk) (stk + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    LiveSep L [((s.regs 4).toNat - stk, (s.regs 4).toNat + above)] ∧
    s.xmm 15 = 0#128 ∧ s.df = false ∧ TlsG s ∧
    Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - stk) (stk + above) ∧ Outside (s.fsBase.toNat - 8) 8 R.rt

@[reducible] def Input (R : RtInv) (L : List (Nat × Nat)) (s : State) (p n : Nat) : Prop :=
  s.mem.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧
    (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧ Apart p (8 * n) ((s.regs 4).toNat - 4288) (4288 + 104)

def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (mp ml mc k n : Nat)
    (s : State) : Prop :=
  Env R L s 4288 104 ∧
    s.mem.readLE ((s.regs 4).toNat + 8) 8 = mp ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = ml ∧
    s.mem.readLE ((s.regs 4).toNat + 24) 8 = mc ∧ s.mem.readLE ((s.regs 4).toNat + 32) 8 = k ∧
    s.mem.readLE ((s.regs 4).toNat + 40) 8 = n ∧
    xl.toNat = n ∧ yl.toNat = n ∧ ml = n ∧ 0 < n ∧ 2 * n ≤ zc.toNat ∧ zc.toNat < 2 ^ 40 ∧
    n ≤ mc ∧ mc < 2 ^ 40 ∧
    s.mem.accessible zp.toNat (8 * zc.toNat) true = true ∧ zp.toNat + 8 * zc.toNat ≤ 2 ^ 48 ∧
    (InRanges zp.toNat (8 * zc.toNat) L ∨ Outside zp.toNat (8 * zc.toNat) R.rt) ∧
    Apart zp.toNat (8 * zc.toNat) ((s.regs 4).toNat - 4288) (4288 + 104) ∧
    Apart ((s.regs 14).toNat + 16) 8 zp.toNat (8 * zc.toNat) ∧
    Apart (s.fsBase.toNat - 8) 8 zp.toNat (8 * zc.toNat) ∧
    s.mem.accessible hasADX 1 false = true ∧
    Input R L s xp.toNat n ∧ Input R L s yp.toNat n ∧ Input R L s mp n ∧
    Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * n) ∧ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * n) ∧
    Apart zp.toNat (8 * zc.toNat) mp (8 * n) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [zp.toNat, 16 * n] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [zp.toNat, zp.toNat + n * 8, n * 8]

def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp yp : BitVec 64) (mp k n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = zp ∧ (s'.regs 3).toNat = n ∧ s'.regs 1 = zc ∧
    s'.mem.readLE zp.toNat (8 * n) =
      montgomery n (s.mem.readLE xp.toNat (8 * n)) (s.mem.readLE yp.toNat (8 * n)) (s.mem.readLE mp (8 * n)) k ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), L' = L ∧ b' = b ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4288, (s.regs 4).toNat + 104)] ++
        [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

set_option hygiene false in
local macro "slotv" : tactic => `(tactic| (
  rw [slot _ (by omega) (by omega) (by omega) (by omega)]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
  try simp only [Nat.reducePow, rmp', rml', rmc', rk', rn', hml, hxl, h_ret']
  try omega))

set_option hygiene false in
local macro "inputv" h:term:max a1:term:max a2:term:max : tactic => `(tactic| (
  have hA1 := $a1
  have hA2 := $a2
  unfold Apart at hA1 hA2
  rw [FvModexp.Expmc.held_readLE $h F LF (hcs _ _ (by omega) (by omega)) (hz16 _ _ (by omega))]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens' (impl : List Amd64.Segment) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (LibMont.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hamv : Summary0 (LibMont.program.link impl) (segAddr LibMont.program amvFn) AmvPre AmvQ)
    (hsub : Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (mp ml mc k n : Nat) :
    Ensures (LibMont.program.link impl) (segAddr LibMont.program fn) [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl yp yl mp ml mc k n) (Post R b L zp zc xp yp mp k n) := by
  intro ret hret s hs hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hwin, hgw, hgrt, hLs, hx15, hdf, htls, hts, htrt⟩, rmp, rml, rmc, rk, rn,
    hxl, hyl, hml, hn, hn2, hzc, hmc, hmc', hzacc, hzp, hzh, hzw, hgz, htz, hadx,
    ⟨hxacc, hxp, hxh, hxw⟩, ⟨hyacc, hyp, hyh, hyw⟩, ⟨hmacc, hmp, hmh, hmw⟩, hzx, hzy, hzm, hinv, hokc, hokm⟩ := hpre
  janus64_intro hs
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have htb := htls.base
  have htr := htls.readable
  have htg := htls.g
  have hLs' : ∀ r ∈ L, Outside r.1 (r.2 - r.1)
      ([((s.regs 4).toNat - 192 - 4096, (s.regs 4).toNat - 192), ((s.regs 4).toNat - 192 + 8, (s.regs 4).toNat - 192 + 8 + 16)] ++
        [((s.regs 4).toNat - 192, (s.regs 4).toNat - 192 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [outside_cons, outside_nil, outside_append, and_true] at this ⊢
    omega
  have hokc' : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [zp.toNat, (n + n) * 8] := by
    rw [show (n + n) * 8 = 16 * n by omega]; exact hokc
  have hzh16 : InRanges zp.toNat ((n + n) * 8) L ∨ Outside zp.toNat ((n + n) * 8) R.rt :=
    hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  janus64_run [rmp, rml, rmc, rk, rn, FvModexp.toInt_add_self n (by omega)] until [head] calls [hclr L b]
  rename_i _ _ _ _ w _ _ F LF IV Zr
  have hzw' := hzw
  unfold Apart at hzw'
  have eA : ∀ a k wr, w.accessible a k wr = s.mem.accessible a k wr := by
    intro a k wr; rw [F.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
  have hcs : ∀ a k, (a + k ≤ (s.regs 4).toNat - 192 - 4096 ∨ (s.regs 4).toNat - 192 ≤ a) →
      (a + k ≤ (s.regs 4).toNat - 192 + 8 ∨ (s.regs 4).toNat - 192 + 8 + 16 ≤ a) →
      Outside a k [((s.regs 4).toNat - 192 - 4096, (s.regs 4).toNat - 192),
        ((s.regs 4).toNat - 192 + 8, (s.regs 4).toNat - 192 + 8 + 16)] := by
    intro a k h1 h2; simp only [outside_cons, outside_nil, and_true]; omega
  have hz16 : ∀ a k, (a + k ≤ zp.toNat ∨ zp.toNat + (n + n) * 8 ≤ a) →
      Outside a k [(zp.toNat, zp.toNat + (n + n) * 8)] := by
    intro a k h; simp only [outside_cons, outside_nil, and_true]; omega
  have slot : ∀ a, (s.regs 4).toNat - 4288 ≤ a → a + 8 ≤ (s.regs 4).toNat + 104 →
      (a + 8 ≤ (s.regs 4).toNat - 192 - 4096 ∨ (s.regs 4).toNat - 192 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 192 + 8 ∨ (s.regs 4).toNat - 192 + 8 + 16 ≤ a) → w.readLE a 8 = _ :=
    fun a h1 h2 h3 h4 => FvModexp.Expmc.slot_read F hwin h1 (by omega) (hcs a 8 h3 h4) (hz16 a 8 (by omega))
  have hretlt := hret.user
  have hX : w.readLE xp.toNat (8 * n) = s.mem.readLE xp.toNat (8 * n) := by inputv hxh hxw hzx
  have hY : w.readLE yp.toNat (8 * n) = s.mem.readLE yp.toNat (8 * n) := by inputv hyh hyw hzy
  have hM : w.readLE mp (8 * n) = s.mem.readLE mp (8 * n) := by inputv hmh hmw hzm
  have hG : w.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    have hA1 := hgw
    have hA2 := hgz
    unfold Apart at hA1 hA2
    rw [F.readLE _ _ (by simp only [outside_append]; exact ⟨⟨hgrt, hcs _ _ (by omega) (by omega)⟩, hz16 _ _ (by omega)⟩)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hkl : k < 2 ^ 64 := by rw [← rk]; simpa using Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 4).toNat + 32) 8
  have hsplt : 4288 ≤ (s.regs 4).toNat := hb'
  have rmp' := rmp
  rw [show (s.regs 4).toNat + 8 = (s.regs 4).toNat - 184 + 192 by omega] at rmp'
  have rml' := rml
  rw [show (s.regs 4).toNat + 16 = (s.regs 4).toNat - 184 + 200 by omega] at rml'
  have rmc' := rmc
  rw [show (s.regs 4).toNat + 24 = (s.regs 4).toNat - 184 + 208 by omega] at rmc'
  have rk' := rk
  rw [show (s.regs 4).toNat + 32 = (s.regs 4).toNat - 184 + 216 by omega] at rk'
  have rn' := rn
  rw [show (s.regs 4).toNat + 40 = (s.regs 4).toNat - 184 + 224 by omega] at rn'
  have h_ret' := h_ret
  rw [show (s.regs 4).toNat = (s.regs 4).toNat - 184 + 184 by omega] at h_ret'
  refine Amd64.Tactic.Reaches.mono (MontLoop.loop (impl := impl) (R := R) (hamv := hamv) (hsub := hsub) (hmv := hmv)
    (ret := ret) (hret := hret) (s := s) (L := L) (b := b) (sp := (s.regs 4).toNat - 184) (zp := zp.toNat)
    (cap := zc.toNat) (xp := xp.toNat) (xc := xc.toNat) (yp := yp.toNat) (mp := mp) (mc := mc) (k := k) (n := n)
    (M0 := w) (hsps := by omega) (hx15 := h_x15) (hal := by omega) (hsp4 := by omega) (hsp48 := by omega)
    (hacc := by rw [eA, show (s.regs 4).toNat - 184 - 4104 = (s.regs 4).toNat - 4288 by omega,
      show 4104 + 288 = 4288 + 104 from rfl]; exact hw)
    (hn := hn) (hn2 := hn2) (hcap := hzc) (hxc := xc.isLt) (hmc := hmc) (hmc' := hmc') (hk := hkl)
    (hzp := hzp) (hzacc := by rw [eA]; exact hzacc) (hxacc := by rw [eA]; exact hxacc) (hxp := hxp)
    (hyacc := by rw [eA]; exact hyacc) (hyp := hyp) (hmacc := by rw [eA]; exact hmacc) (hmp := hmp)
    (hadx := by rw [eA]; exact hadx)
    (hzx := hzx) (hzy := hzy) (hzm := hzm)
    (hzs := by unfold Apart; omega) (hxs := by have := hxw; unfold Apart at this ⊢; omega)
    (hys := by have := hyw; unfold Apart at this ⊢; omega) (hms := by have := hmw; unfold Apart at this ⊢; omega)
    (r60 := by slotv) (r68 := by slotv) (ra0 := by slotv) (rc0 := by slotv) (rc8 := by slotv) (rd0 := by slotv)
    (rd8 := by slotv) (re0 := by slotv) (r100 := by slotv) (r108 := by slotv) (r110 := by slotv) (r118 := by slotv)
    (hret0 := by slotv) (hbp := by slotv)
    (htb := htb) (htr := by rw [eA]; exact htr)
    (htg := by
      have hA1 := hts; have hA2 := htz; unfold Apart at hA1 hA2
      rw [F.readLE _ _ (by simp only [outside_append]; exact ⟨⟨htrt, hcs _ _ (by omega) (by omega)⟩, hz16 _ _ (by omega)⟩)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact htg)
    (hts := by have := hts; unfold Apart at this ⊢; omega) (htz := htz)
    (hg := hg1) (hgacc := by rw [eA]; exact hg2) (hgs := by have := hgw; unfold Apart at this ⊢; omega) (hgz := hgz)
    (hguard := by rw [hG]; omega) (hgrt := hgrt)
    (hwin := by rw [show 4104 + 288 = 4288 + 104 from rfl, show (s.regs 4).toNat - 184 - 4104 = (s.regs 4).toNat - 4288 by omega]; exact hwin)
    (hzh := hzh) (hLs := fun r hr => by
      have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)
    (hinv := IV) (hok := hokm) n _ 0 0 w (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (MemFrame.refl _ _) ?_ rfl) ?_
  all_goals first
    | rfl
    | (janus64_simp [FvModexp.Expmc.bv_ofNat_toNat, h_x15, h_df, Nat.two_mul]; done)
    | (janus64_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | skip
  · rw [show 8 * (2 * n) = (n + n) * 8 by omega, FvModexp.Expmc.readLE_zeroed Zr]; rfl
  · intro o ho
    cases o with
    | stub _ _ _ => exact ho.elim
    | returned s' =>
      simp only [isReturn_returned] at ho ⊢
      obtain ⟨e1, e2, e3, e4, ed, efs, e5, e6, e7, ev, ei, ef, el⟩ := ho
      have hF0 : MemFrame s.mem w (R.rt ++ [((s.regs 4).toNat - 4288, (s.regs 4).toNat + 104),
          (zp.toNat, zp.toNat + (n + n) * 8)]) := by janus_frame
      have hL0 : LiveFrame s.mem w L [(zp.toNat, zp.toNat + (n + n) * 8)] := by
        refine ⟨fun a k hin hout => ?_⟩
        rw [LF.readLE a k hin hout]
        obtain ⟨r, hr, h1, h2⟩ := hin
        have := hLs r hr
        simp only [outside_cons, outside_nil, and_true] at this
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      refine ⟨⟨e1, e2, e3, e4⟩, efs, by rw [ed, hdf], by rw [e5, FvModexp.Expmc.bv_ofNat_toNat], by rw [e6]; simp; omega,
        by rw [e7, FvModexp.Expmc.bv_ofNat_toNat], by rw [ev, hX, hY, hM], L, b, rfl, rfl, ei, ?_, ?_⟩
      · refine hF0.trans ef (fun a k hk => ?_)
        simp only [outside_append, outside_cons, outside_nil, and_true] at hk ⊢
        exact ⟨⟨hk.1.1, by omega, by omega⟩, ⟨hk.1.1, by omega, by omega⟩⟩
      · refine FvModexp.Expmc.liveFrame_widen (hL0.trans (FvModexp.Expmc.liveFrame_widen el ?_) (fun _ _ h => h)) ?_
        · intro a k h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
        · intro a k h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

end FvModexp.Amd64.Mont

namespace FvModexp.Amd64.Mont

open Janus.Contracts.EqHashModel

/-- `ens'` in the project's statement shape (docs/CONVENTIONS.md §3): restricted Run program, runtime contracts
about `Extracted.program.ofImpl impl`, `ImplApart`; the asm kernels are agent asm's verified summaries (`MontAsm`). -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (mp ml mc k n : Nat) :
    Ensures ((Extracted.program.onlySegments LibMont.names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl yp yl mp ml mc k n) (Post R b L zp zc xp yp mp k n) := by
  have hc := Amd64.codeIn_ofImpl_restrict_of_apart64 hap LibMont.names
  have e3 : segAddr Extracted.program fn = segAddr LibMont.program fn := by decide
  rw [← LibMont.eq_only] at hc ⊢
  rw [e3]
  exact ens' impl R (MemclrNoHeapPointersLive64.of_codeIn hc hclr) (MemmoveLive64.of_codeIn hc hmv)
    (MontAsm.amv_sum impl) (MontAsm.sub_sum impl) b L
    zp zl zc xp xl xc yp yl yc mp ml mc k n

end FvModexp.Amd64.Mont
