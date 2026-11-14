import FvModexp.Proofs.Amd64.Exp.SlowU3
import FvModexp.Proofs.Amd64.Exp.SlowUJR

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the upper join — `KJ1` (`j1`) → `KT1` at `j + 1`, `v <<= 1` (agent expmc s81; twin of
arm64 `SlowJF`'s join)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem wsJ1_own {sp K : Nat} (hK : K + 8 ≤ sp) : ∀ r ∈ wsJ1 sp, OwnR sp K r := by
  intro r hr
  simp only [wsJ1, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega

theorem rdJ1 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' (wsJ1 sp)) :
    m'.readLE (sp + 0x138) 8 = m.readLE (sp + 0x138) 8 ∧ m'.readLE (sp + 0x160) 8 = m.readLE (sp + 0x160) 8 ∧
    (∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, fun a k h1 _ => hF.readLE _ _ ?_⟩ <;>
  simp only [wsJ1, outside_cons, outside_nil, and_true] <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the upper join**: `KJ1` → `KT1` (`j + 1`, `v + v`), the stack header kept -/
theorem segUJ (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)}
    {b1 j w : Nat} {v : BitVec 64} {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KJ1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 j w v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (KT : ∀ S' : State, KT1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 (j + 1) w (v + v) z zl
      zc' Zv zz zzl zzc rr rl rc q ql qc → stCap S'.mem st = stCap S.mem st →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hk.jc.wc.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  have hjw := hk.jw
  have hw63 := hk.w63
  obtain ⟨bzz, bzzc⟩ := hk.bb.bzz.lt64
  obtain ⟨bq, bqc⟩ := hk.bb.bq.lt64
  obtain ⟨-, brc⟩ := hk.bb.br.lt64
  have hzzl := hk.bb.lzz
  have hql := hk.bb.lq
  have hrl := hk.bb.lr
  obtain ⟨-, -, sl1b8, sl1c0, -, -, -, -, -, sl200, sl208, sl210, sl218⟩ := hk.jc.esl
  refine runJ1 ret0 Q sp j xp st xc yl yp w xl zz zzl zzc q ql qc rl v S.mem hacc (by omega) hK5 (by omega) bzz
    (by omega) bzzc bq (by omega) bqc (by omega) hk.sb8 sl208 sl200 sl218 sl1c0 sl1b8 hk.s138 sl210 S hk.pc
    hk.jc.esp rfl hk.e8 hk.e6 hk.e7 hk.e15 hk.e11 hk.e9 hk.e12 hk.e2 ?_
  intro T tpc t4 tF trg ma8 ma0 m90 m168 m78 m70 m150 t0 t10 t8 t2 t1 t13 t15 t3 t6 t7 t9 t11 t12 t14 tfs tx tdf
  obtain ⟨hw2, hdl2, hln2⟩ := WC.own hP hk.jc.wc tF trg (wsJ1_own hK3)
  obtain ⟨u138, u160, ukw⟩ := rdJ1 tF
  have hj2 := hk.jc.call (S' := T) (t4.trans hk.jc.esp.symm) t14 tfs tx tdf hw2 ukw
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  have hcap : stCap T.mem st = stCap S.mem st :=
    tF.readLE _ _ (by simp only [wsJ1, outside_cons, outside_nil, and_true]; omega)
  exact KT T ⟨hj2, BB.tr hdl2 hln2 hk.bb, hw63, u138.trans hk.s138, tpc, hk.zlb, by omega, t0.trans hk.e0,
    t10.trans hk.e3, t8.trans hk.e1, m150, m70, m78, u160.trans hk.s160, m90, t2.trans hk.e13, m168, ma0, ma8, t1,
    t13, t15, t3, t6, t7, t9, t11, t12⟩ hcap

end

end FvModexp.Amd64.ExpSlow
