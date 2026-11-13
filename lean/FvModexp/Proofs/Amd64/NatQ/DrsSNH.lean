import FvModexp.Proofs.Amd64.NatQ.DrsSNI
import FvModexp.Proofs.Amd64.NatQ.DrsPro2d

set_option autoImplicit false

/-! (amd64 twin of the pure half of Arm64/NatQ/DrsSN.lean, asm s45)
# `divRecursiveStep` (amd64), big path: the loop head invariant at `j = m` from the facts after `stk.nat(B + 1)`

`sl_init` (the fixed slots from `AtN0`), `head_mk` (`H` at `j = m`). Used by DrsSN `callN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the fixed slots at the head from `AtN0`'s (pure) -/
theorem sl_init {c : Cx} {s P : State} {T S : Memory} {rs : List (Nat × Nat)}
    (hA : AtN0 s P c.qp c.ql c.qc c.st c.up c.u1 c.uc c.vp c.vl c.vc c.d)
    (hvp : s.mem.readLE ((s.regs 4).toNat + 8) 8 = c.vp) (hvl : s.mem.readLE ((s.regs 4).toNat + 16) 8 = c.vl)
    (hvc : s.mem.readLE ((s.regs 4).toNat + 24) 8 = c.vc) (hMF : MemFrame P.mem T rs) (hfo : FixOut s rs)
    (hM2 : MemFrame T S [((s.regs 4).toNat - 232, (s.regs 4).toNat - 216), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56)])
    (h0 : 400 ≤ (s.regs 4).toNat)
    (q1 : S.readLE ((s.regs 4).toNat - 232) 8 = c.vl / 2 + 1) (q2 : S.readLE ((s.regs 4).toNat - 224) 8 = c.vl / 2 + 1)
    (q3 : S.readLE ((s.regs 4).toNat - 64) 8 = c.t0) : Sl c s S := by
  have hF := hA.fr
  have hP : ∀ x n, Outside x n rs → Outside x n [((s.regs 4).toNat - 232, (s.regs 4).toNat - 216), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56)] →
      S.readLE x n = P.mem.readLE x n := fun x n h1 h2 => by rw [hM2.readLE x n h2, hMF.readLE x n h1]
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hfo
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N →
      Outside x n [((s.regs 4).toNat - 232, (s.regs 4).toNat - 216), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56)] →
      S.readLE x n = P.mem.readLE x n := fun hA h1 h2 h3 => hP _ _ (hA.of_sub h1 h2) h3
  have oo : ∀ x n, (x + n ≤ (s.regs 4).toNat - 232 ∨ (s.regs 4).toNat - 216 ≤ x) → (x + n ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 56 ≤ x) →
      Outside x n [((s.regs 4).toNat - 232, (s.regs 4).toNat - 216), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56)] := by
    intro x n a b; simp only [outside_cons, outside_nil, and_true]; omega
  exact ⟨by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hF.ra,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hF.bp,
    by rw [r o1 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dbit, q1, q2,
    by rw [r o2 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.mm,
    by rw [r o3 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.nn,
    by rw [r o4 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.bb,
    by rw [r o5 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.uu, q3,
    by rw [r o6 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dfn,
    by rw [r o6 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dst,
    by rw [r o6 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dn,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.dp,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega)), hF.vp]; exact hvp,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega)), hF.vl]; exact hvl,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega)), hF.vc]; exact hvc,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s1,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s2,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s3,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s4,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s5,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s7,
    by rw [r o7 (by omega) (by omega) (oo _ _ (by omega) (by omega))]; exact hA.s9⟩

set_option maxHeartbeats 16000000 in
/-- **the head invariant at `j = m`** from the facts after the call (pure) -/
theorem head_mk {R : RtInv} {c : Cx} {s P S : State} {T : Memory} {rs : List (Nat × Nat)} {bk : Nat}
    (hcr : Cr R c s) (hev : Ev R c s c.L1 bk T) (hfp : Fp R c s c.L1 T (c.l1 s))
    (hkeep : ∀ x k, Held R c.L x k → Outside x k (win s c.W 96) → Apart x k c.st 24 →
      Apart x k (stW s.mem c.st + 8 * stLen s.mem c.st) (8 * (stCap s.mem c.st - stLen s.mem c.st)) →
      T.readLE x k = s.mem.readLE x k)
    (hA : AtN0 s P c.qp c.ql c.qc c.st c.up c.u1 c.uc c.vp c.vl c.vc c.d) (hMF : MemFrame P.mem T rs) (hfo : FixOut s rs)
    (hb1 : c.b - stkR c.Hq s.mem c.st + stkR c.Hq T c.st ≤ bk)
    (hpc : S.rip = BitVec.ofNat 64 head) (hsp : S.regs 4 = s.regs 4 - 392#64) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hx15 : S.xmm 15 = 0#128)
    (h0 : S.regs 0 = BitVec.ofNat 64 c.t0) (h3 : S.regs 3 = BitVec.ofNat 64 (c.vl / 2 + 1))
    (h1 : S.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)) (h2 : S.regs 2 = BitVec.ofNat 64 (c.u1 - c.vl))
    (hM2 : MemFrame T S.mem [((s.regs 4).toNat - 232, (s.regs 4).toNat - 216), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56)])
    (hreg : S.mem.regions = T.regions)
    (q1 : S.mem.readLE ((s.regs 4).toNat - 232) 8 = c.vl / 2 + 1) (q2 : S.mem.readLE ((s.regs 4).toNat - 224) 8 = c.vl / 2 + 1)
    (q3 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = c.t0) :
    H R c s c.L1 bk S (c.u1 - c.vl) := by
  have hW := hcr.hW; have := drsW64_ge c.vl
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  have hv2 := hpre.v2; have htop := hpre.vtop; have hq0 := hpre.q0
  obtain ⟨-, -, hqh, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huw, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvw, -, -, -⟩ := hpre.va
  obtain ⟨hqs, hqf⟩ := hpre.sq
  obtain ⟨hus, huf⟩ := hpre.su
  obtain ⟨hvs, hvf⟩ := hpre.sv2
  have hcb := hpre.cost
  have hfw : MemFrame T S.mem (fw s) := hM2.mono fun x k ho => by
    simp only [fw, win, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hk2 : ∀ x k, Held R c.L x k → Outside x k (win s c.W 96) → Apart x k c.st 24 →
      Apart x k (stW s.mem c.st + 8 * stLen s.mem c.st) (8 * (stCap s.mem c.st - stLen s.mem c.st)) →
      S.mem.readLE x k = s.mem.readLE x k := fun x k a b c d => by
    rw [hfw.readLE x k (by simp only [win, fw, outside_cons, outside_nil, and_true] at b ⊢; omega)]
    exact hkeep x k a b c d
  have hsub : ∀ {x k : Nat}, c.up ≤ x → x + k ≤ c.up + 8 * c.ul → S.mem.readLE x k = s.mem.readLE x k :=
    fun h1 h2 => hk2 _ _ (huh.sub h1 h2) (huw.of_sub h1 h2) (by unfold Apart at hus ⊢; omega)
      (by unfold Apart at huf ⊢; omega)
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have eq : natVal S.mem c.qp c.ql = 0 := by
    show S.mem.readLE c.qp (8 * c.ql) = 0
    rw [hk2 _ _ hqh hqw hqs hqf]; exact hq0
  have eu : natVal S.mem c.up c.u1 = natVal s.mem c.up c.u1 := hsub (Nat.le_refl _) (by omega)
  refine ⟨hpc, hsp, h5, h14, hfs, hdf, hx15, h0, h3, h1, h2, hcr, hev.own hcr hfw hreg, hfp.own hcr hfw,
    sl_init hA hpre.vpS hpre.vlS hpre.vcS hMF hfo hM2 (by omega) q1 q2 q3, li_init (by omega) hvu htop eq eu _,
    hk2 _ _ hvh hvw hvs hvf, hsub (by omega) (by omega), ?_⟩
  exact bud_init hcb.2 hcr.h40 hvu hu1 (by rw [stkR_congr (hcr.capOwn hfw)]; exact hb1)

end FvModexp.Amd64.Q.DivRec
