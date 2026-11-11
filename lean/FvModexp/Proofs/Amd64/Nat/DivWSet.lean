import FvModexp.Proofs.Amd64.Nat.DivWMid
import FvModexp.Proofs.Common.AsmVW
import FvModexp.Proofs.Common.DivmcBits

/-!
# `nat.divW` (amd64): `case y == 1: q = z.set(x)` (`m > 0`), from `+0x1b2` (after `z.make(m)`)

At `+0x1b2`: `AX = p`, `CX = c`, `DX = SI = m`, `DI = xp`. `CMPQ DX, SI; MOVQ SI, BX; CMOVL` (`min`);
`CMPQ DI, AX; JE` (no copy when the pointers agree); spills `0x58, 0x70, 0x60(RSP')` (`RSP - 40, -16, -32`);
`memmove(p, xp, 8 m)`; `return z[:m], 0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

abbrev hSet : Nat := segAddr Extracted.program fn + 0x1b2

theorem div_one (n : Nat) : n / (1#64 : BitVec 64).toNat = n := by simp
theorem mod_one (n : Nat) : n % (1#64 : BitVec 64).toNat = 0 := by simp [Nat.mod_one]

theorem Mid.setPost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hxv : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (hxn : M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0)
    (hF : MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 4232, (s.regs 4).toNat - 8), (p, p + 8 * xl.toNat)]))
    (hLF : LiveFrame M M' L' [(p, p + 8 * xl.toNat)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M'))
    (hcp : M'.readLE p (8 * xl.toNat) = M.readLE xp.toNat (8 * xl.toNat))
    (hnz : M'.readLE (p + 8 * (xl.toNat - 1)) 8 = M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8)
    (s' : State) (hm : s'.mem = M') (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 3).toNat = xl.toNat)
    (h2 : (s'.regs 1).toNat = c) (h3 : (s'.regs 7).toNat = 0) (hfs : s'.fsBase = s.fsBase) :
    Post R b L zp zc xp xl 1#64 s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  refine ⟨hfs, p, xl.toNat, c, h0, h1, h2, by rw [h3, mod_one], ?_, Or.inr ?_, hcap, Nat.le_refl _, L', b', h.ext,
    h.bud, hinv, fun _ => ⟨h.p8, h.pheld, by rw [hF.accessible]; exact h.pacc, h.p48⟩, h.ror, ?_, ?_⟩
  · rw [div_one, show natVal s'.mem p xl.toNat = s'.mem.readLE p (8 * xl.toNat) from rfl, hcp]; exact hxv
  · rw [hnz]; exact hxn
  · refine h.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz⟩ := ho
    refine ⟨hrt, by omega, ?_⟩
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · omega
    · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n (h.ext.inRanges_old hin) ?_]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      simp only [outside_cons, outside_nil, and_true] at hz ⊢
      rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
      · omega
      · have := hap q hq; unfold Apart at this; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setTail (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M)
    (hxv : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (hxn : M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h2 : S.regs 2 = xl) (h1 : S.regs 1 = BitVec.ofNat 64 c) (h7 : S.regs 7 = xp) (h6 : S.regs 6 = xl)
    (hsp : S.regs 4 = s.regs 4 - 128#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ Post R b L zp zc xp xl 1#64 s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hx0 := h.x0; have hx48 := h.x48
  have r1 := h.lr; have r2 := h.fp; have hsacc := h.sacc; have hal := h.al; have hinv := h.inv
  have hpacc : M.accessible p (8 * xl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc := h.xacc; have hra := h.ra47; have hwrt := h.wrt
  have hpw := h.pw; have hxw := h.xw; have hgw := h.gw; have hpf := h.pf; have hpg := h.pg; have htw := h.tw
  unfold Apart at hpw hxw hgw hpf hpg htw
  have hph : InRanges p (xl.toNat * 8) L' ∨ Outside p (xl.toNat * 8) R.rt := h.pheld.sub (Nat.le_refl _) (by omega)
  have hx15' := h.x15
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, xl.toNat * 8] := fun d src => h.mv d src _ (by omega)
  have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc; have htacc := h.tacc; have htls := h.tls; have htb := h.tlsg.base; have htrt := h.trt
  have hgok : M.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 136 := by
    rw [h.grd]; have := h.gok; omega
  janus64_run [hm, r1, r2, hfs, BitVec.msb_eq_decide, FvModexp.mod64_of_lt c (by omega),
    FvModexp.mod64_of_lt p (by omega)] calls [hmv]
  · -- `p = xp`: no copy
    rename_i hpx
    have hpx' : xp.toNat = p := by omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, h.setPost hxv hxn (MemFrame.refl _ _) ⟨fun _ _ _ _ => rfl⟩ h.inv (by rw [hpx'])
      (by rw [hpx']) _ rfl ?_ ?_ ?_ ?_ ?_⟩
    all_goals try janus64_simp
    all_goals first | exact hx15'.symm | omega
  · rename_i _ _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp
    have hcp' := Asm.readLE_of_copied hcp
    have hsub : Mem.Copied _ m (p + 8 * (xl.toNat - 1)) (xp.toNat + 8 * (xl.toNat - 1)) 8 := fun i hi => by
      have := hcp (8 * (xl.toNat - 1) + i) (by omega)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at this; exact this
    have hnz' := Asm.readLE_of_copied hsub
    have hW : MemFrame M ((((M.writeLE ((s.regs 4).toNat - 40) 8 c).writeLE ((s.regs 4).toNat - 16) 8 p).writeLE
        ((s.regs 4).toNat - 32) 8 xl.toNat).writeLE ((s.regs 4).toNat - 136) 8 6219429)
        [((s.regs 4).toNat - 136, (s.regs 4).toNat - 128), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32),
          ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)] := by
      janus_frame
    have rdW : ∀ a n, (a + n ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 8 ≤ a) →
        ((((M.writeLE ((s.regs 4).toNat - 40) 8 c).writeLE ((s.regs 4).toNat - 16) 8 p).writeLE
          ((s.regs 4).toNat - 32) 8 xl.toNat).writeLE ((s.regs 4).toNat - 136) 8 6219429).readLE a n = M.readLE a n :=
      fun a n h' => hW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [show xl.toNat * 8 = 8 * xl.toNat by omega] at hF2 hLF2 hcp'
    refine ⟨⟨?_, ?_, ?_, ?_⟩, h.setPost hxv hxn (hW.trans hF2 fun a n ho => ?fr) ⟨fun a n hin ho => ?lf⟩ hinv2 ?cp
      ?nz _ rfl ?_ ?_ ?_ ?_ ?_⟩
    case fr =>
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2'⟩ := ho
      and_intros <;> first | exact hr | omega
    case lf =>
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this
      rw [hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ ho, rdW a n (by omega)]
    case cp => rw [hcp', rdW _ _ (by omega)]
    case nz => rw [hnz', rdW _ _ (by omega)]
    all_goals try janus64_simp
    all_goals first | exact hx15'.symm | omega

end FvModexp.Amd64.DivW
