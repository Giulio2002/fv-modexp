import FvModexp.Proofs.Amd64.Nat.RshFin
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.rsh` (amd64): `s = 0`, `cap z = 0`: `z.set(x)` — from the join of `z.make(len x)` (`+0xf2`) to the return

`CMPQ DX, SI; CMOVL` (`n = min(len x, len z) = len x`); `CMPQ DI, AX; JE` (not taken: fresh `z`); spills
`e - 16 = p`, `e - 32 = len`, `e - 56 = c`; `memmove(p, x, 8 len x)` (`+0x121`); reloads; `RET` (no `norm`: `x` is
normalised).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Rsh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem copyS (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibRsh.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc x xl 0 s p c L' b' M) (hN : NatNorm s.mem x xl)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hJoinS) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h2 : S.regs 2 = BitVec.ofNat 64 xl) (h6 : S.regs 6 = BitVec.ofNat 64 xl)
    (h7 : S.regs 7 = BitVec.ofNat 64 x)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibRsh.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc x xl 0 s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hpx := h.px
  simp only [need, Nat.zero_div, Nat.sub_zero] at hcap
  unfold Apart at hpx
  have hxl0 := h.n0; simp only [need, Nat.zero_div, Nat.sub_zero] at hxl0
  have hc40 := h.c40; have hp48 := h.p48
  have hx16 := h.xl16; have hx48 := h.x48
  have r1 := h.lr; have r2 := h.fp; have hsacc := h.sacc; have hal := h.al
  have hpacc : M.accessible p (xl * 8) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc : M.accessible x (xl * 8) false = true := by rw [show xl * 8 = 8 * xl by omega]; exact h.xacc
  have hx15' := h.x15; have hra := h.ra47; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hpf := h.pf; have htw := h.tw
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hpw hgw hpg hpf htw
  have hph : InRanges p (xl * 8) L' ∨ Outside p (xl * 8) R.rt := h.pheld.sub (Nat.le_refl _) (by omega)
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, xl * 8] := fun d src => h.sv.2.1 d src _ (by omega)
  have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc; have htacc := h.tacc; have htls := h.tls; have htb := h.tlsg.base; have htrt := h.trt
  have hgok : M.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 152 := by
    rw [h.grd]; have := h.gok; omega
  have hinv := h.inv
  have hc' : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hl' : xl % 18446744073709551616 = xl := Nat.mod_eq_of_lt (by omega)
  have hpx' : (BitVec.ofNat 64 x = BitVec.ofNat 64 p) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hne : ((18446744073709551616 - p + x) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; omega
  janus64_run [hm, r1, r2, hc', hl', hpx', hne, hfs, BitVec.msb_eq_decide] calls [hmv]
  rename_i _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp
  have hW : MemFrame M ((((M.writeLE ((s.regs 4).toNat - 16) 8 p).writeLE ((s.regs 4).toNat - 32) 8 xl).writeLE
      ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 152) 8 6187750)
      [((s.regs 4).toNat - 152, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48),
        ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)] := by
    janus_frame
  have rdW : ∀ a k, (a + k ≤ (s.regs 4).toNat - 152 ∨ (s.regs 4).toNat - 8 ≤ a) →
      ((((M.writeLE ((s.regs 4).toNat - 16) 8 p).writeLE ((s.regs 4).toNat - 32) 8 xl).writeLE
        ((s.regs 4).toNat - 56) 8 c).writeLE ((s.regs 4).toNat - 152) 8 6187750).readLE a k = M.readLE a k :=
    fun a k h' => hW.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  rw [show xl * 8 = 8 * xl by omega] at hF2 hLF2 hcp
  have hrd : ∀ a k, p ≤ a → a + k ≤ p + 8 * xl → m.readLE a k = s.mem.readLE (a - p + x) k := fun a k h1 h2 => by
    have hsub : Janus.Contracts.Mem.Copied _ m a (a - p + x) k := fun i hi => by
      have := hcp (a - p + i) (by omega)
      rw [show p + (a - p + i) = a + i by omega, show x + (a - p + i) = a - p + x + i by omega] at this
      exact this
    rw [Asm.readLE_of_copied hsub, rdW _ _ (by omega)]; exact h.xr _ _ (by omega) (by omega)
  have hv : natVal m p xl = natVal s.mem x xl / 2 ^ 0 := by
    simp only [natVal, Nat.pow_zero, Nat.div_one]; rw [hrd _ _ (Nat.le_refl _) (Nat.le_refl _)]; simp
  have hn : NatNorm m p xl := by
    rcases hN with h0 | h0
    · exact Or.inl h0
    · right; rw [hrd _ _ (by omega) (by omega), show p + 8 * (xl - 1) - p + x = x + 8 * (xl - 1) by omega]
      exact h0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, h.post (hW.trans hF2 fun a k ho => ?fr) ⟨fun a k hin ho => ?lf⟩ hinv2 _ xl ?hm2
    ?_ ?_ ?_ ?_ hcap hv hn⟩
  case hm2 => rfl
  case fr =>
    simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hr, h1', h2'⟩ := ho
    and_intros <;> first | exact hr | omega
  case lf =>
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ho
    rw [hLF2.readLE a k ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega),
      rdW a k (by omega)]
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hfs | exact hdf | exact hx15'.symm | skip

end FvModexp.Amd64.Rsh
