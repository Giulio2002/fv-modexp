import FvModexp.Proofs.Amd64.Exp.SubMod2NGAlloc

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: `J3G` → the `append` loop (`for len(z)*64 < n { z = append(z, 0) }`,
nat.go:1748-1750, with its `growslice` path) → `J4G` (agent infra s48; twin of Arm64/Exp/SubMod2NGS4A.lean)

Loop test at `+0x300` (`RAX = p`, `RBX = len`, `RCX = cap`, `RDX = n`); `+0x30c`: `len + 1 ≤ cap` → store `0` at
`+0x2f7`; otherwise `growslice` at `+0x321` (return `+0x326`), `RDX = n` reloaded, then the store.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
  FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-- the difference the loop carries -/
@[reducible] def dD (s : State) (zp zl yp yl n : Nat) : Nat := natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n

/-- the loop invariant at the test `+0x300` -/
@[reducible] def AI (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl n : Nat) (s S : State)
    (p l c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat) : Prop :=
  S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) ∧ Abi s S ∧
    S.regs 0 = BitVec.ofNat 64 p ∧ S.regs 3 = BitVec.ofNat 64 l ∧ S.regs 1 = BitVec.ofNat 64 c ∧
    S.regs 2 = BitVec.ofNat 64 n ∧ Fw s S.mem zp zl zc yp n ∧ Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 ∧
    NatLive S.mem R L3 p c ∧ CurA R L zp zc p c ∧ c < 2 ^ 40 ∧ p < 2 ^ 64 ∧ l ≤ c ∧ l ≤ W n ∧ g ≤ l ∧
    (W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) ∧ natVal S.mem p l = dD s zp zl yp yl n

theorem natVal_store_top' (m : Memory) (p k v a : Nat) (ha : a = p + 8 * k) (hv : v < 2 ^ 64) :
    natVal (m.writeLE a 8 v) p (k + 1) = natVal m p k + 2 ^ (64 * k) * v := by
  subst ha; exact natVal_store_top m p k v hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `growslice` entry (`c = l < ⌈n/64⌉`) to the next test, with the fresh array -/
theorem gstep (impl : List Amd64.Segment) {R : RtInv}
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {p l c g : Nat} {L3 : List (Nat × Nat)} {b3 : Nat}
    (T : State) (hpc : T.rip = BitVec.ofNat 64 (cA "runtime.growslice"))
    (hsp : T.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 136)) (hab : Abi s T)
    (hra : T.mem.readLE ((s.regs 4).toNat - 136) 8 = 6216646)
    (h0 : (T.regs 0).toNat = p) (h3 : (T.regs 3).toNat = l + 1) (h1 : (T.regs 1).toNat = c)
    (h7 : (T.regs 7).toNat = 1) (h6 : (T.regs 6).toNat = wT)
    (hfw : Fw s T.mem zp zl zc yp n) (hrt : Rt R (b - g * gA n) L s zp zc n 3 T.mem L3 b3)
    (hlv : NatLive T.mem R L3 p c) (hcur : CurA R L zp zc p c) (hp64 : p < 2 ^ 64) (hcl : c = l)
    (hlW : l + 1 ≤ W n) (hg : g ≤ l)
    (hgz : W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) (hv : natVal T.mem p l = dD s zp zl yp yl n)
    (K : ∀ (S' : State) (p' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), S'.rip = BitVec.ofNat 64 6216608 →
      AI R b L zp zl zc yp yl n s S' p' (l + 1) c' (g + 1) L' b' → GoalG impl R b L zp zl zc yp yl n s S') :
    GoalG impl R b L zp zl zc yp yl n s T := by
  have hzW : zc < W n := Nat.lt_of_not_le fun h => by
    have := (hgz h).2.1; omega
  have hcG : costG n ≤ b := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 hzW
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have hs4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hout := hpre.1.2.2.2.2.1
  simp only [K, A] at hout
  have hround : growsliceRound64 T = 8 * growCap8 (l + 1) c := by simp only [growsliceRound64, h3, h1]
  have hgr8 := growRoundG (N := l + 1) (c := c) (n := n) (by omega) hlW
  obtain ⟨hbr, hbud⟩ := bud_grow (r := 8 * growCap8 (l + 1) c) hcG (by omega) hrt.2.2.2.2.1 hgr8
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 136 := by rw [hsp, BitVec.toNat_ofNat]; omega
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  unfold GoalG
  refine ReachesRet.call_regions (hgr L3 b3) hpc
    (gcallG hpre hrt hlv hcur hcl hlW hbr T rfl hspT h14 (by rw [hspT, hra]; decide) h0 h3 h1 h7 h6)
    fun S1 hpc1 hpost hrg1 => ?_
  obtain ⟨ptr, junk, f1, x1, yh1, m1, zh1, kr1, hs1, hMF, hLF, ⟨hobj, hapL⟩, hapS, hinv1⟩ := hpost
  subst hs1
  rw [hround] at hapL hinv1
  simp only [growsliceObj64, Fresh, h3, h1, h7] at hobj
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, hcopy, -⟩ := hobj
  simp only [calleeStack64, hspT] at hMF
  rw [h14] at hinv1
  have hgcl := le_growCap8 (l + 1) c
  have hgcb := growCapG_lt (N := l + 1) (c := c) (n := n) (by omega) hlW hn15
  have hrt1 := rt_alloc (B' := b - (g + 1) * gA n) hrt hs4 hrg1 hMF hLF hpin hapL hbud hinv1
  have hfw1 := fw_alloc hs4 hout hfw hMF
  have r8 : m1.readLE ((s.regs 4).toNat - 136 + 8 + 136) 8 = n := by
    rw [show (s.regs 4).toNat - 136 + 8 + 136 = (s.regs 4).toNat + 8 by omega]; exact hfw1.2.2.2.2.2.2
  have hval1 : natVal m1 ptr.toNat l = natVal T.mem p l := by
    refine natVal_copy fun i hi => ?_
    rw [← h0]; exact hcopy i (by omega)
  have hpw := fresh_win hout hpin
  have hT3 : T.regs 3 = BitVec.ofNat 64 (l + 1) := by rw [← h3, Expmc.bv_ofNat_toNat]
  have hacc1 : m1.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hMF.accessible, hrt.2.1.accessible]; exact hpre.1.2.1.2.2
  have hcurN : CurA R L zp zc ptr.toNat (growCap8 (l + 1) c) := Or.inr ⟨hpin, fresh_of hrt.2.2.2.1 hapL⟩
  have hlvN : NatLive m1 R (L3 ++ [(ptr.toNat, ptr.toNat + 8 * growCap8 (l + 1) c)]) ptr.toNat (growCap8 (l + 1) c) :=
    fun _ => ⟨hal8 (Or.inr (by omega)), Or.inl (inRanges_snoc _ _ _), hpacc, hp48⟩
  rw [h1] at *
  janus64_run [r8, hT3, hspT] until [6216608]
  refine K _ ptr.toNat (growCap8 (l + 1) c) (L3 ++ [(ptr.toNat, ptr.toNat + 8 * growCap8 (l + 1) c)])
    (b3 - 8 * growCap8 (l + 1) c) ?_ ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, BitVec.isLt _, ?_, ?_,
      ?_, ?_, ?_⟩
  all_goals try janus64_simp
  all_goals first
    | exact h14 | exact hfs | exact hx15 | exact hdf
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hspT]; omega)
    | exact fw_cstore hfw1 (by omega) hs4
    | exact rt_cstore hrt1 hcurN hlvN (by omega) (by omega)
    | exact natLive_store hlvN _ _ _
    | exact hcurN | exact hgcb | exact hgcl | exact hlW | exact hg | exact fun h => by omega
    | (rw [natVal_store_top' _ _ _ _ _ (by omega) (by decide), hval1, hv]; simp)
    | skip

end FvModexp.Amd64.SubMod2N

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- one test of the append loop (at `+0x300`) -/
theorem appIterG (impl : List Amd64.Segment) {R : RtInv}
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (k4 : J4G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n)
    (S : State) (p l c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat) (hpc : S.rip = BitVec.ofNat 64 6216608)
    (hI : AI R b L zp zl zc yp yl n s S p l c g L3 b3)
    (KL : ∀ (S' : State) (p' c' g' : Nat) (L' : List (Nat × Nat)) (b' : Nat), l + 1 ≤ W n →
      S'.rip = BitVec.ofNat 64 6216608 → AI R b L zp zl zc yp yl n s S' p' (l + 1) c' g' L' b' →
      GoalG impl R b L zp zl zc yp yl n s S') :
    GoalG impl R b L zp zl zc yp yl n s S := by
  obtain ⟨hsp, ⟨h14, hfs, hx15, hdf⟩, h0, h3, h1, h2, hfw, hrt, hlv, hcur, hc40, hp64, hlc, hlW, hg, hgz, hv⟩ := hI
  have hs4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hn15 := hpre.2.2.2.2.2.2.2.1
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hpre.1.2.1.2.2
  simp only [W] at hlW
  have hsh : (BitVec.ofNat 64 l <<< 6).toNat = 64 * l := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  unfold GoalG
  by_cases hc : n ≤ 64 * l
  · have hlW' : l = (n + 63) / 64 := by omega
    subst hlW'
    janus64_run [hc, hsh] until [6216656]
    refine k4 _ p c g L3 b3 hpre ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ hfw hrt hlv hcur hc40 hp64 hlc hg hgz hlt hv
    all_goals first | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | janus64_simp
  · by_cases hcap : l + 1 ≤ c
    · have hw1 := (curA_win hpre hcur).1
      obtain ⟨-, -, hpacc, hp48⟩ := hlv (by omega)
      janus64_run [hc, hsh, hcap] until [6216608]
      refine KL _ p c g L3 b3 (by simp only [W]; omega) ?_ ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hp64, ?_, ?_, ?_, hgz, ?_⟩
      all_goals try janus64_simp
      all_goals first
        | exact h14 | exact hfs | exact hx15 | exact hdf
        | exact fw_cstore hfw (by omega) hs4
        | exact rt_cstore hrt hcur hlv (by omega) (by omega)
        | exact natLive_store hlv _ _ _
        | exact hcur | exact hc40 | exact hcap
        | (simp only [W]; omega)
        | omega
        | (rw [natVal_store_top' _ _ _ _ _ (by omega) (by decide), hv]; simp)
        | skip
    · have hcl : c = l := by omega
      have hs136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
      janus64_run [hc, hsh, hcap, hs136] until [cA "runtime.growslice"]
      refine gstep impl hgr hpre _ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcur hp64 hcl
        (by simp only [W]; omega) hg hgz ?_
        fun S' p' c' L' b' hpc' hI' => KL S' p' c' (g + 1) L' b' (by simp only [W]; omega) hpc' hI'
      all_goals try janus64_simp
      all_goals first
        | exact h14 | exact hfs | exact hx15 | exact hdf
        | exact hfw | exact hrt | exact hlv | exact hv
        | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
        | omega
        | skip

theorem appG (impl : List Amd64.Segment) {R : RtInv}
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (k4 : J4G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    (hlt : natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n) :
    ∀ (k : Nat) (S : State) (p l c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat), W n - l = k →
      S.rip = BitVec.ofNat 64 6216608 → AI R b L zp zl zc yp yl n s S p l c g L3 b3 →
      GoalG impl R b L zp zl zc yp yl n s S := by
  intro k
  induction k with
  | zero =>
    intro S p l c g L3 b3 hk hpc hI
    exact appIterG impl hgr k4 hpre hlt S p l c g L3 b3 hpc hI fun _ _ _ _ _ _ h => absurd h (by omega)
  | succ k ih =>
    intro S p l c g L3 b3 hk hpc hI
    exact appIterG impl hgr k4 hpre hlt S p l c g L3 b3 hpc hI
      fun S' p' c' g' L' b' hl1 hpc' hI' => ih S' p' (l + 1) c' g' L' b' (by omega) hpc' hI'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s4aG (impl : List Amd64.Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) (k4 : J4G impl R b L op zp zl zc yp yl yc n s) : J3G impl R b L op zp zl zc yp yl yc n s := by
  intro S p3 l3 c3 L3 b3 hpre hpc hsp hab h0 h3 h1 hfw hrt hlv hcur hc40 hp64 hlc hgz hlt hv hn hl3
  have hs4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have r8 : S.mem.readLE ((s.regs 4).toNat - 128 + 136) 8 = n := by
    rw [show (s.regs 4).toNat - 128 + 136 = (s.regs 4).toNat + 8 by omega]; exact hfw.2.2.2.2.2.2
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hrt.2.1.accessible]; exact hpre.1.2.1.2.2
  have hrt0 : Rt R (b - 0 * gA n) L s zp zc n 3 S.mem L3 b3 := by simpa only [Nat.zero_mul, Nat.sub_zero] using hrt
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  unfold GoalG
  janus64_run [r8] until [6216608]
  refine appG impl hgr k4 hpre hlt _ _ p3 l3 c3 0 L3 b3 rfl ?_ ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hfw, hrt0, hlv, hcur,
    hc40, hp64, hlc, hl3, Nat.zero_le _, fun h => ⟨(hgz h).1, (hgz h).2, rfl⟩, hv⟩
  all_goals first | (janus64_simp; done) | exact h14 | exact hfs | exact hx15 | exact hdf | janus64_simp

end FvModexp.Amd64.SubMod2N
