import FvModexp.Proofs.Amd64.Exp.SlowK2
import FvModexp.Proofs.Amd64.Exp.SlowXUR

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the two loop exits into the word test `iT` (agent asm s74; twin of arm64 `SlowXU`)

* `itS`: the word test `iT` with `R11 = t - 1` (`t ≤ len y - 1`): `t = 0` → `KE` at `ex`; `t = i + 1` → `KT2` at `t2`
  with `j = 0`, `v = y[i]` (nat.go:766-769);
* `exitU`: `KT1` with `j = w` (`JGE t1x`) → `iT` with `t = len y - 1` (nat.go:749, 766);
* `exitL`: `KT2` with `j = 64` (`JGE iS`) → `iT` with `t = i`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- `JC` through a run that keeps the memory and the frame registers -/
theorem JC.keepM {S S' : State} {L1 : List (Nat × Nat)} {b1 : Nat}
    (h : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1) (hm : S'.mem = S.mem)
    (h4 : S'.regs 4 = S.regs 4) (h14 : S'.regs 14 = S.regs 14) (hf : S'.fsBase = S.fsBase)
    (hx : S'.xmm 15 = S.xmm 15) (hd : S'.df = S.df) :
    JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 :=
  ⟨h4.trans h.esp, h14.trans h.e14, by rw [hf]; exact h.efs, hx.trans h.ex15, hd.trans h.edf, by rw [hm]; exact h.wc,
    by rw [hm]; exact h.esl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the word test `iT`** (see the module doc) -/
theorem itS {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 t : Nat}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hpc : S.rip = BitVec.ofNat 64 iT)
    (hj : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1)
    (hB : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc) (hzl : zl ≤ max xl ml) (ht : t < yl)
    (e0 : S.regs 0 = BitVec.ofNat 64 z) (e10 : S.regs 10 = BitVec.ofNat 64 zl)
    (e8 : S.regs 8 = BitVec.ofNat 64 zc') (s150 : S.mem.readLE (sp + 0x150) 8 = zz)
    (s70 : S.mem.readLE (sp + 0x70) 8 = zzl) (s78 : S.mem.readLE (sp + 0x78) 8 = zzc)
    (s160 : S.mem.readLE (sp + 0x160) 8 = rr) (e1 : S.regs 1 = BitVec.ofNat 64 rl)
    (e2 : S.regs 2 = BitVec.ofNat 64 rc) (s168 : S.mem.readLE (sp + 0x168) 8 = q)
    (e13 : S.regs 13 = BitVec.ofNat 64 ql) (e15 : S.regs 15 = BitVec.ofNat 64 qc)
    (e3 : S.regs 3 = BitVec.ofNat 64 xl) (e6 : S.regs 6 = BitVec.ofNat 64 xp) (e7 : S.regs 7 = BitVec.ofNat 64 st)
    (e12 : S.regs 12 = BitVec.ofNat 64 yp) (e11 : S.regs 11 = BitVec.ofNat 64 t - 1#64)
    (KXE : ∀ S' : State, t = 0 →
      KE R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc →
      stCap S'.mem st = stCap S.mem st → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), t = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 i 0 v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc → stCap S'.mem st = stCap S.mem st → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.1
  rcases t with _ | i
  · have e11' : S.regs 11 = BitVec.ofNat 64 18446744073709551615 := by rw [e11]; decide
    refine runEX ret0 Q S hpc e11' fun S' pc' hm hr hf hx hd => KXE S' rfl
      ⟨hj.keepM hm (congrFun hr 4) (congrFun hr 14) hf hx hd, by rw [hm]; exact hB, pc', hzl,
        by rw [hr]; exact e0, by rw [hr]; exact e10, by rw [hr]; exact e8⟩ (by rw [hm])
  · have e11' : S.regs 11 = BitVec.ofNat 64 i := by
      rw [e11]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hw := hj.wc
    have hwacc := hP.cenv0.2.2.2.1
    have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
      rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
    have hyw := y_words hP hw i (by omega)
    have hya : s.mem.accessible yp (8 * yl) false = true := hP.2.2.2.2.2.2.2.1
    have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.1
    have hyA : Apart yp (8 * yl) (sp - 8 - K) (K + 0x228) := hP.2.2.2.2.2.2.1.2.1
    unfold Apart at hyA
    have hya1 : S.mem.accessible (yp + i * 8) 8 false = true := by
      rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hya (by omega) (by omega)
    refine runIX ret0 Q sp yp i S.mem hacc (by omega) hK5 (by omega) (by omega) hya1 (by omega) S hpc hj.esp rfl e11'
      e12 ?_
    intro S2 pc2 hF hrg mc0 mb0 g9 gk gfs gx gdf
    obtain ⟨hw2, hdl2, hln2⟩ := WC.own hP hw hF hrg (fun q hq => by
      simp only [FI, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
    have hFo : ∀ a k, (a + k ≤ sp + 0xb0 ∨ sp + 0x198 ≤ a ∨ (sp + 0xc8 ≤ a ∧ a + k ≤ sp + 0x190) ∨
        (sp + 0xb8 ≤ a ∧ a + k ≤ sp + 0xc0)) → Outside a k (FI sp) := by
      intro a k ha; simp only [FI, outside_cons, outside_nil, and_true]; omega
    have kF : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → S2.mem.readLE a k = S.mem.readLE a k :=
      fun a k h1 _ => hF.readLE a k (hFo a k (Or.inr (Or.inl (by omega))))
    have hj2 := hj.call (S' := S2) (gk 4 (by decide)) (gk 14 (by decide)) gfs gx gdf hw2 kF
    have hB2 : BB R L st zp zc S2.mem L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc :=
      ⟨hln2 _ _ _ _ hB.bz, hdl2 _ _ hB.bzz, hB.lzz, hdl2 _ _ hB.br, hB.lr, hdl2 _ _ hB.bq, hB.lq, hB.p1, hB.p2,
        hB.p3, hB.p4, hB.p5, hB.p6⟩
    have hv : (BitVec.ofNat 64 (S.mem.readLE (yp + i * 8) 8)).toNat = Exp.wd (natVal s.mem yp yl) i := by
      have := readLE_lt_8 S.mem (yp + i * 8)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]; exact hyw
    exact KX2 S2 i _ rfl hv ⟨hj2, hB2, by omega, mc0, mb0, pc2, hzl, Nat.zero_le _,
      (gk 0 (by decide)).trans e0, (gk 10 (by decide)).trans e10, (gk 8 (by decide)).trans e8,
      (hF.readLE _ _ (hFo _ _ (by omega))).trans s150, (hF.readLE _ _ (hFo _ _ (by omega))).trans s70,
      (hF.readLE _ _ (hFo _ _ (by omega))).trans s78, (hF.readLE _ _ (hFo _ _ (by omega))).trans s160,
      (gk 1 (by decide)).trans e1, (gk 2 (by decide)).trans e2, (hF.readLE _ _ (hFo _ _ (by omega))).trans s168,
      (gk 13 (by decide)).trans e13, (gk 15 (by decide)).trans e15, g9, (gk 11 (by decide)).trans e11',
      (gk 3 (by decide)).trans e3, (gk 6 (by decide)).trans e6, (gk 7 (by decide)).trans e7⟩
      (by
        obtain ⟨hstw, -⟩ := hP.stkF
        unfold Apart at hstw
        exact hF.readLE _ _ (by simp only [FI, outside_cons, outside_nil, and_true]; omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the upper loop's exit** (`t1` with `j = w` → `iT`, `t = len y - 1`) -/
theorem exitU {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 w w v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (KXE : ∀ S' : State, yl - 1 = 0 →
      KE R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), yl - 1 = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 i 0 v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := hk.jc.wc
  have hwacc := hP.cenv0.2.2.2.1
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runTX ret0 Q sp yl w S.mem hacc (by omega) hK5 hyl0 hyl hk.w63 S hk.pc hk.jc.esp rfl hk.e1 hk.e15 hk.e11 ?_
  intro S2 pc2 hm g11 g13 g15 g1 gk gfs gx gdf
  refine itS hP pc2 (hk.jc.keepM hm (gk 4 (by decide) (by decide) (by decide) (by decide))
    (gk 14 (by decide) (by decide) (by decide) (by decide)) gfs gx gdf) (by rw [hm]; exact hk.bb) hk.zlb
    (by omega : yl - 1 < yl) ((gk 0 (by decide) (by decide) (by decide) (by decide)).trans hk.e0)
    ((gk 10 (by decide) (by decide) (by decide) (by decide)).trans hk.e10)
    ((gk 8 (by decide) (by decide) (by decide) (by decide)).trans hk.e8) (by rw [hm]; exact hk.s150)
    (by rw [hm]; exact hk.s70) (by rw [hm]; exact hk.s78) (by rw [hm]; exact hk.s160) (by rw [g1, hk.s90])
    ((gk 2 (by decide) (by decide) (by decide) (by decide)).trans hk.e2) (by rw [hm]; exact hk.s168)
    (by rw [g13, hk.sa0]) (by rw [g15, hk.sa8]) ((gk 3 (by decide) (by decide) (by decide) (by decide)).trans hk.e3)
    ((gk 6 (by decide) (by decide) (by decide) (by decide)).trans hk.e6)
    ((gk 7 (by decide) (by decide) (by decide) (by decide)).trans hk.e7)
    ((gk 12 (by decide) (by decide) (by decide) (by decide)).trans hk.e12) g11 (fun S' h0 hke _ => KXE S' h0 hke)
    (fun S' i v h1 h2 hk2 _ => KX2 S' i v h1 h2 hk2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the lower loop's exit** (`t2` with `j = 64` → `iS` → `iT`, `t = i`) -/
theorem exitL {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 i : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i 64 v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (KXE : ∀ S' : State, i = 0 →
      KE R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc →
      stCap S'.mem st = stCap S.mem st → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i' : Nat) (v : BitVec 64), i = i' + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i' →
      KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 i' 0 v z zl zc' Zv zz zzl zzc
        rr rl rc q ql qc → stCap S'.mem st = stCap S.mem st → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hiy := hk.iy
  have hw := hk.jc.wc
  have hwacc := hP.cenv0.2.2.2.1
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runSX ret0 Q sp i S.mem hacc (by omega) hK5 (by omega) hk.sb0 S hk.pc hk.jc.esp rfl hk.e11 ?_
  intro S2 pc2 hm g11 g9 g12 gk gfs gx gdf
  refine itS hP pc2 (hk.jc.keepM hm (gk 4 (by decide) (by decide) (by decide))
    (gk 14 (by decide) (by decide) (by decide)) gfs gx gdf) (by rw [hm]; exact hk.bb) hk.zlb
    (by omega : i < yl) ((gk 0 (by decide) (by decide) (by decide)).trans hk.e0)
    ((gk 10 (by decide) (by decide) (by decide)).trans hk.e10)
    ((gk 8 (by decide) (by decide) (by decide)).trans hk.e8) (by rw [hm]; exact hk.s150)
    (by rw [hm]; exact hk.s70) (by rw [hm]; exact hk.s78) (by rw [hm]; exact hk.s160)
    ((gk 1 (by decide) (by decide) (by decide)).trans hk.e1) ((gk 2 (by decide) (by decide) (by decide)).trans hk.e2)
    (by rw [hm]; exact hk.s168) ((gk 13 (by decide) (by decide) (by decide)).trans hk.e13)
    ((gk 15 (by decide) (by decide) (by decide)).trans hk.e15) ((gk 3 (by decide) (by decide) (by decide)).trans hk.e3)
    ((gk 6 (by decide) (by decide) (by decide)).trans hk.e6) ((gk 7 (by decide) (by decide) (by decide)).trans hk.e7)
    (by rw [g12, hk.jc.esl.2.2.1]) g11 (fun S' h0 hke hc => KXE S' h0 hke (by rw [hc, hm]))
    (fun S' i' v h1 h2 hk2 hc => KX2 S' i' v h1 h2 hk2 (by rw [hc, hm]))

end

end FvModexp.Amd64.ExpSlow
