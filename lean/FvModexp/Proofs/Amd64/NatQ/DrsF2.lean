import FvModexp.Proofs.Amd64.NatQ.DrsFRecP
import FvModexp.Proofs.Amd64.NatQ.DrsFRecQ
import FvModexp.Proofs.Amd64.NatQ.DrsNormF1
import FvModexp.Proofs.Common.DivmcBits

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF2.lean; adapted from Amd64/NatQ/DrsB2.lean)
# `divRecursiveStep` (amd64), final block segment 2: the recursive call (natdiv.go:862)

`f2`: from `AF1` (`0x5f00e5`) → `u[s:]` (`len` spilled at `0x60(SP)`), `normF1` (`u[s:].norm()`, length `n'`) →
`f2x`: the slots of `BdF` (`0x118/0x110/0x108/0x128/0x100/0xf8/0x170(SP)`), `v[s:]` on the stack, `depth + 1` →
`CALL divRecursiveStep` at `0x5f022e` → `f2c`: the induction hypothesis → its return `0x5f0233` (`AF2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the dividend argument of the final recursive call is small (from the loop invariant at `j ≤ B`) -/
theorem argF_lt {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} {M : Memory} (hcr : Cr R c s)
    (hli : c.LI s j Z U) (hj : j ≤ c.vl / 2) (huk : Asm.limbs M c.up c.u1 = U) :
    2 * natVal M (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) <
      2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) := by
  obtain ⟨-, hu, -, hul, -, -, htail, -⟩ := hli
  have h40 := hcr.h40; have hvu := hcr.vu1
  have htail' : ∀ d ∈ U.drop (c.vl + c.vl / 2), d = 0 := by
    intro d hd
    have e : U.drop (c.vl + c.vl / 2) = (U.drop (j + c.vl)).drop (c.vl / 2 - j) := by
      rw [List.drop_drop]; congr 1; omega
    rw [e] at hd
    exact htail d (List.mem_of_mem_drop hd)
  have hlt : Mdl.val U < 2 ^ (64 * (c.vl + c.vl / 2)) := Mdl.lt_of_drop_zero hu htail'
  have e0 : natVal M (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) = Mdl.val (U.drop (c.vl / 2 - 1)) := by
    rw [← huk, drop_limbs_v (by omega), Asm.val_limbs]; rfl
  have e1 : Mdl.val (U.drop (c.vl / 2 - 1)) = Mdl.val U / 2 ^ (64 * (c.vl / 2 - 1)) := (Mdl.val_take_mod U _ hu).2
  have h2 : Mdl.val U / 2 ^ (64 * (c.vl / 2 - 1)) < 2 ^ (64 * (c.vl + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Mdl.pow64_add]
    exact Nat.lt_of_lt_of_le hlt (Mdl.pow_le_pow_64 (by omega))
  rw [e0, e1]
  have e2 : 2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) = 2 ^ (64 * (c.vl + 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e2]
  have : 2 ≤ 2 ^ 64 := by decide
  have := Nat.mul_le_mul_left (2 ^ (64 * (c.vl + 1))) this
  omega

/-- the own stores of segment 2: the return slot and stack arguments of the call, `len u[s:]` and the `BdF` slots -/
@[reducible] def isF2 (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 400, (s.regs 4).toNat - 368), ((s.regs 4).toNat - 296, (s.regs 4).toNat - 288),
    ((s.regs 4).toNat - 144, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88),
    ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the final block's recursive call, from the callee entry `X` (the induction hypothesis) -/
theorem f2c (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : AF1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', AF2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (n' : Nat) (hk : n' ≤ c.u1 - (c.vl / 2 - 1))
    (hkv : natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) n' = natVal S.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)))
    (hkN : NatNorm S.mem (c.up + 8 * (c.vl / 2 - 1)) n')
    (X : State) (hpc : X.rip = BitVec.ofNat 64 0x5ef880) (hsp : X.regs 4 = s.regs 4 - 400#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hdf : X.df = false) (hx15 : X.xmm 15 = 0#128)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h3 : X.regs 3 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h7 : X.regs 7 = BitVec.ofNat 64 c.st)
    (h6 : X.regs 6 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1))) (h8 : X.regs 8 = BitVec.ofNat 64 n')
    (h9 : X.regs 9 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1)))
    (hF8 : MemFrame S.mem X.mem (isF2 s)) (hreg : X.mem.regions = S.mem.regions)
    (hra : X.mem.readLE ((s.regs 4).toNat - 400) 8 = rF2)
    (a1 : X.mem.readLE ((s.regs 4).toNat - 392) 8 = c.vp + 8 * (c.vl / 2 - 1))
    (a2 : X.mem.readLE ((s.regs 4).toNat - 384) 8 = c.vl - c.vl / 2 + 1)
    (a3 : X.mem.readLE ((s.regs 4).toNat - 376) 8 = c.vc - (c.vl / 2 - 1))
    (e1 : X.mem.readLE ((s.regs 4).toNat - 112) 8 = c.vl / 2 - 1)
    (e2 : X.mem.readLE ((s.regs 4).toNat - 296) 8 = c.u1 - (c.vl / 2 - 1))
    (e3 : X.mem.readLE ((s.regs 4).toNat - 120) 8 = c.uc - (c.vl / 2 - 1))
    (e4 : X.mem.readLE ((s.regs 4).toNat - 128) 8 = 8 * (c.vl / 2 - 1))
    (e5 : X.mem.readLE ((s.regs 4).toNat - 96) 8 = c.up + 8 * (c.vl / 2 - 1))
    (e6 : X.mem.readLE ((s.regs 4).toNat - 144) 8 = c.vl - (c.vl / 2 - 1))
    (e7 : X.mem.readLE ((s.regs 4).toNat - 136) 8 = c.vc - (c.vl / 2 - 1))
    (e8 : X.mem.readLE ((s.regs 4).toNat - 24) 8 = c.vp + 8 * (c.vl / 2 - 1)) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q := by
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have huc := hpre.ulc; have huc4 := hpre.uc40; have hv9 := hpre.v9.1
  have hu48 := hpre.ua.2.1
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hj := hA.jB
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF : MemFrame S.mem X.mem (fw s) := hF8.mono fun x n ho => by
    simp only [fw, win, isF2, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hA.ev hF hreg
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := Fp.own hcr hA.fp hF
  have rd8 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF8.readLE _ _ (by simp only [win, isF2, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hBdX : BdF c s X.mem Z :=
    ⟨hA.sl.frame hF8 (by simp only [FixOut, isF2, outside_cons, outside_nil, and_true]; omega), e1, e2, e3, e4, e5,
      e6, e7, e8, by rw [rd8 _ _ hvw]; exact hA.vk, by rw [rd8 _ _ (huw.of_sub (by omega) (by omega))]; exact hA.utl,
      by rw [limbs_congr (rd8 _ _ hqw)]; exact hA.zk⟩
  have huk : Asm.limbs X.mem c.up c.u1 = U := by
    rw [limbs_congr (rd8 _ _ (huw.of_sub (by omega) (by omega)))]; exact hA.uk
  have hq0 : X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = 0 := by rw [rd8 _ _ hcr.t0w]; exact hA.q0
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → X.mem.readLE x n = S.mem.readLE x n := fun x n h1 h2 =>
    rd8 _ _ (huw.of_sub h1 h2)
  have hkvX : natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) n' =
      natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) := by
    simp only [natVal] at hkv ⊢
    rw [ru _ _ (by omega) (by omega), ru _ _ (by omega) (by omega)]; exact hkv
  have hkNX : NatNorm X.mem (c.up + 8 * (c.vl / 2 - 1)) n' := by
    rcases hkN with h | h
    · exact Or.inl h
    · right; rw [ru _ _ (by omega) (by omega)]; exact h
  have hval0 := argF_lt (M := X.mem) hcr hA.li hj huk
  have hval : 2 * natVal X.mem (c.up + 8 * (c.vl / 2 - 1)) n' <
      2 ^ (64 * (c.vl - c.vl / 2 + 1 + (c.vl / 2 + 1))) := by rw [hkvX]; exact hval0
  have hbX := bud_cap (Cr.capOwn hcr hF) hA.bud
  have hKb : drsCQ c.ul (c.vl - c.vl / 2 + 1) + stkR c.Hq X.mem c.st ≤ bk := by
    have h1 : drsCQ c.ul (c.vl - c.vl / 2 + 1) ≤ c.K s := by simp only [Cx.K]; omega
    have h3 := hbX
    omega
  have hrp := rec_preF hcr hEvX hFpX hBdX.vk hk hval hq0 hspn h14 hfs hKb a1 a2 a3
  have tn : ∀ {r : BitVec 64} {v : Nat}, r = BitVec.ofNat 64 v → v < 2 ^ 64 → r.toNat = v := fun h hv => by
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have t0 := tn h0 (by have := hcr.t048; omega); have t3 := tn h3 (by omega); have t1 := tn h1 (by omega)
  have t7 := tn h7 (by have := Janus.Arm64.Memory.readLE_lt S.mem ((s.regs 4).toNat + 56) 8; rw [hA.sl.s4] at this; omega)
  have t6 := tn h6 (by omega); have t8 := tn h8 (by omega); have t9 := tn h9 (by omega)
  refine ReachesRet.call_regions (ih ⟨c.Hq, bk, Lk, c.W - 400, X.regs 0, X.regs 3, X.regs 1, X.regs 7, X.regs 6,
    X.regs 8, X.regs 9, X.regs 10, c.vp + 8 * (c.vl / 2 - 1), c.vl - c.vl / 2 + 1, c.vc - (c.vl / 2 - 1)⟩) hpc
    ⟨⟨⟨by rw [hspn, hra]; decide, hx15, hdf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?hw, ?hp⟩, ?hmu⟩ ?hk
  case hw =>
    show drsW64 (c.vl - c.vl / 2 + 1) ≤ c.W - 400
    have := drsW64_inner h40; omega
  case hp =>
    show DrsPreW R bk Lk c.Hq (drsCQ (X.regs 8).toNat (c.vl - c.vl / 2 + 1)) (c.W - 400)
      (X.regs 0).toNat (X.regs 3).toNat (X.regs 1).toNat (X.regs 7).toNat (X.regs 6).toNat (X.regs 8).toNat
      (X.regs 9).toNat (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) (c.vc - (c.vl / 2 - 1)) X
    rw [t0, t1, t3, t6, t7, t8, t9]; exact hrp
  case hmu =>
    show c.vl - c.vl / 2 + 1 < c.vl
    omega
  case hk =>
    intro X' hpc' ⟨hK, hpost⟩ hrg
    change DrsPostW R bk Lk c.Hq (drsCQ (X.regs 8).toNat (c.vl - c.vl / 2 + 1)) (c.W - 400)
      (X.regs 0).toNat (X.regs 3).toNat (X.regs 7).toNat (X.regs 6).toNat (X.regs 8).toNat
      (c.vp + 8 * (c.vl / 2 - 1)) (c.vl - c.vl / 2 + 1) X X' at hpost
    rw [t0, t3, t6, t7, t8] at hpost
    have hfs' := hpost.1; have hdf' := hpost.2.1
    obtain ⟨L', b', hEv, hFp, hBd, hqk, huk', hbud⟩ :=
      rec_postF hcr hEvX hFpX hBdX hk huk hkvX hkNX hspn h14 hbX hpost hrg
    obtain ⟨k1, k2, k3, k4⟩ := hK
    exact k L' b' X' ⟨by rw [hpc']; simp only [retAddrOf]; rw [hspn, hra], by rw [k1]; exact sp_ret400 hspn (by omega),
      by rw [k2, h5], by rw [k3, h14], by rw [hfs', hfs], by rw [hdf', hdf], by rw [k4, hx15], hcr,
      hEv, hFp, hBd, hj, hA.li, hqk, huk', hbud⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from the exit of `normF1` (`0x5f0180`) to the recursive call -/
theorem f2x (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : AF1 R c s Lk bk S j Z U) (Q : State → Prop)
    (k : ∀ L' b' S', AF2 R c s L' b' S' j Z U → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q)
    (S0 : State) (M1 : Memory) (hM1 : MemFrame S.mem M1 (isF2 s)) (hreg1 : M1.regions = S.mem.regions)
    (hr296 : M1.readLE ((s.regs 4).toNat - 296) 8 = c.u1 - (c.vl / 2 - 1))
    (hsp0 : S0.regs 4 = s.regs 4 - 392#64) (h5 : S0.regs 5 = s.regs 4 - 8#64) (h14 : S0.regs 14 = s.regs 14)
    (hfs : S0.fsBase = s.fsBase) (hdf : S0.df = false) (hx15 : S0.xmm 15 = 0#128)
    (h0 : S0.regs 0 = BitVec.ofNat 64 c.t0) (h1 : S0.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h3 : S0.regs 3 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h11 : S0.regs 11 = BitVec.ofNat 64 (c.vl / 2))
    (h2 : S0.regs 2 = BitVec.ofNat 64 (8 * (c.vl / 2 - 1)))
    (h13 : S0.regs 13 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)))
    (h6 : S0.regs 6 = BitVec.ofNat 64 (c.vl / 2 - 1)) (h7 : S0.regs 7 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1))) :
    ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 nExF1 → s'.mem = M1 → s'.regs 12 = BitVec.ofNat 64 n' →
      Same2 12 10 S0 s' → n' ≤ c.u1 - (c.vl / 2 - 1) →
      natVal M1 (c.up + 8 * (c.vl / 2 - 1)) n' = natVal M1 (c.up + 8 * (c.vl / 2 - 1)) (c.u1 - (c.vl / 2 - 1)) →
      NatNorm M1 (c.up + 8 * (c.vl / 2 - 1)) n' → ReachesRet (LibDrs.program.link impl) (retAddrOf s) s' Q := by
  intro P n' hpc hm h12 hS hle hv hN
  have hcr := hA.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hWg := drsW64_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have huc := hpre.ulc; have huc4 := hpre.uc40; have hv9 := hpre.v9.1
  have hvlc := hpre.vlc; have hvc4 := hpre.vc40
  have hu48 := hpre.ua.2.1; have hv48 := hpre.va.2.1
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  have hsl1 : Sl c s M1 := hA.sl.frame hM1 (by simp only [FixOut, isF2, outside_cons, outside_nil, and_true]; omega)
  have g : ∀ r, r ≠ 12 → r ≠ 10 → P.regs r = S0.regs r := fun r a b => hS.1 r a b
  have p0 := (g 0 (by decide) (by decide)).trans h0; have p1 := (g 1 (by decide) (by decide)).trans h1
  have p3 := (g 3 (by decide) (by decide)).trans h3; have p11 := (g 11 (by decide) (by decide)).trans h11
  have p2 := (g 2 (by decide) (by decide)).trans h2; have p13 := (g 13 (by decide) (by decide)).trans h13
  have p6 := (g 6 (by decide) (by decide)).trans h6; have p7 := (g 7 (by decide) (by decide)).trans h7
  have p4 := (g 4 (by decide) (by decide)).trans hsp0; have p5 := (g 5 (by decide) (by decide)).trans h5
  have p14 := (g 14 (by decide) (by decide)).trans h14
  have pfs := hS.2.1.trans hfs; have pdf := hS.2.2.1.trans hdf; have px15 := hS.2.2.2.trans hx15
  have haccS : M1.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hM1.accessible, hA.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hsl1.nn; have r2 := hsl1.vc; have r3 := hsl1.vp; have r4 := hsl1.s9; have r5 := hsl1.s4
  have bv : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a + b < 2 ^ 64 → BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b)) ∧
      (b ≤ a → BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b)) := fun a b ha hb => by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have lt1 : (BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1)) < BitVec.ofNat 64 n') = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have lt2 : (BitVec.ofNat 64 c.vl < BitVec.ofNat 64 (c.vl / 2 - 1)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have one : (1#64) = BitVec.ofNat 64 1 := rfl
  have v1 := (bv c.vc (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have v2 := (bv (c.vc - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  rw [← one, show c.vc - c.vl / 2 + 1 = c.vc - (c.vl / 2 - 1) by omega] at v2
  have n1 := (bv c.vl (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have n2 := (bv (c.vl - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  rw [← one] at n2
  have m2 : ((0#64 - BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1))).sshiftRight 63 &&& BitVec.ofNat 64 (8 * (c.vl / 2 - 1))) =
      BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) :=
    neg_sshr63_and _ _ (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
  have pv := (bv (8 * (c.vl / 2 - 1)) c.vp (by omega) (by omega)).1 (by omega)
  rw [show 8 * (c.vl / 2 - 1) + c.vp = c.vp + 8 * (c.vl / 2 - 1) by omega] at pv
  janus64_run [hm, r1, r2, r3, r4, r5, lt1, lt2, v1, v2, n1, n2, m2, pv, BitVec.msb_eq_decide]
    until [0x5ef880]
  refine f2c impl R c ih s Lk bk S j Z U hA Q k n' hle ?kv ?kN _ rfl ?sp ?r5 ?r14 pfs rfl px15 ?r0 ?r3 ?r1 ?r7 ?r6
    ?r8 ?r9 ?fr ?reg ?ra ?a1 ?a2 ?a3 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8
  case kv =>
    have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M1.readLE x n = S.mem.readLE x n := fun x n h1 h2 =>
      hM1.readLE _ _ (by
        have := huw.of_sub h1 h2
        simp only [win, isF2, outside_cons, outside_nil, and_true] at this ⊢; omega)
    simp only [natVal] at hv ⊢
    rw [← ru _ _ (by omega) (by omega), ← ru _ _ (by omega) (by omega)]; exact hv
  case kN =>
    rcases hN with h | h
    · exact Or.inl h
    · right
      have := huw.of_sub (a := c.up + 8 * (c.vl / 2 - 1) + 8 * (n' - 1)) (n := 8) (by omega) (by omega)
      rw [← hM1.readLE _ _ (by simp only [win, isF2, outside_cons, outside_nil, and_true] at this ⊢; omega)]; exact h
  case fr =>
    refine (Janus.Contracts.Libc.memFrame_trans hM1 (rs' := isF2 s) ?_).mono fun x n ho => ?_
    · unfold isF2; janus_frame
    · simp only [outside_append]; exact ⟨ho, ho⟩
  case reg => rw [← hreg1]; janus64_simp
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact p5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact p14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact p0
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact p3
  case r1 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact p1
  case r7 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r6 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r8 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r9 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case e2 => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])); exact hr296
  all_goals ((repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega)

end FvModexp.Amd64.Q.DivRec
