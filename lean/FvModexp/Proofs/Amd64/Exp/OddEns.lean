import FvModexp.Proofs.Amd64.Exp.OddFun
import FvModexp.Proofs.Amd64.Exp.OddInv

set_option autoImplicit false

/-!
# `nat.expNNOdd` (amd64): `ens` (CONVENTIONS §3; agent expmc s64; twin of `Arm64.ExpOdd.ens`)

`z.expNNOdd(stk, x, y, m)` returns `x^y mod m` (see `PreD`/`PostD`): `pro`, then window-4 (`ExpW4.ens` at `K - 0x78`,
`len y > 1`) or window-2 (`ExpW2.ens` at `K + 0xa0`) as `Summary`s of `LibOdd` (`hypSumO`), then `epi`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.ExpOdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNNOdd`** (amd64): `z.expNNOdd(stk, x, y, m)` returns `x^y mod m` (see `PreD`/`PostD`) -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW4 : nsD.contains W4Loop.fn = false) (hnsW2 : nsD.contains W2Loop.fn = false)
    (b : Nat) (L : List (Nat × Nat)) (K : Nat) (hKD : stkD + 0x78 ≤ K)
    (costD zp zl zc st xp xl xc yp ylen mp n mc : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc]
      (PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc)
      (PostD R b L K costD zp zc st xp xl yp ylen mp n) := by
  refine Ensures.of_old (preD_inv R b L K costF costD zp zc st xp xl xc yp ylen mp n mc _ _ _) ?_
  rw [show names = LibOdd.names from rfl, ← LibOdd.eq_only, show segAddr Extracted.program fn = fnO by decide]
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hPA, hK, hK2, hzA, hc0, hstnz, hMo, hM1, hB⟩ := hpre
  have hge := rsp_ge hPA.1.1
  have hPA' := hPA
  obtain ⟨⟨-, -, -, -, -, -, -, -, hCE, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hyl',
    -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -, -, -, -, -, -, r0, r1, r2, r3, r4, -⟩ := hPA'
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, -⟩ := hCE
  have hr48 := hret.user
  have ht48 : (s.regs 4).toNat + 8 ≤ 2 ^ 48 := by omega
  have hrd : ∀ {a k : Nat}, Apart a k ((s.regs 4).toNat - 0x388 - 8 - K) (K + 0x400) → ∀ {M : Memory},
      MemFrame s.mem M (pw (s.regs 4).toNat) → M.readLE a k = s.mem.readLE a k :=
    fun h _ hF => hF.readLE _ _ (out_pw h (by omega))
  refine returns_of_reaches (pro impl ret hret _ (s.regs 4).toNat (s.regs 14).toNat yp ylen mp n mc s.mem
    (by omega) (by omega) (s.mem.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)) hg1 hg2 (by omega) hyl'
    (by rw [show (s.regs 4).toNat + 8 = (s.regs 4).toNat - 0x388 + 0x390 by omega]; exact r0)
    (by rw [show (s.regs 4).toNat + 0x10 = (s.regs 4).toNat - 0x388 + 0x398 by omega]; exact r1)
    (by rw [show (s.regs 4).toNat + 0x20 = (s.regs 4).toNat - 0x388 + 0x3a8 by omega]; exact r2)
    (by rw [show (s.regs 4).toNat + 0x28 = (s.regs 4).toNat - 0x388 + 0x3b0 by omega]; exact r3)
    (by rw [show (s.regs 4).toNat + 0x30 = (s.regs 4).toNat - 0x388 + 0x3b8 by omega]; exact r4)
    s h_rip (ofNat_self _).symm (ofNat_self _).symm rfl ?K4 ?K2)
  case K4 =>
    intro hy S M' c_pc c_sp c0 c3 c1 c7 c6 c8 c9 c14 cfs cdf cx cm hF hrg q_ra q_bp q0 q1 q2 q3 q4
    subst cm
    have hFw : MemFrame s.mem S.mem [((s.regs 4).toNat - 0x388 - 8 - K, (s.regs 4).toNat - 0x388 + 0x3f8)] :=
      hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hSsp : (S.regs 4).toNat = (s.regs 4).toNat - 0x78 := by rw [c_sp]; exact tN (by omega)
    have hAt : AtCall ((s.regs 4).toNat - 0x388) yp ylen mp n mc s S :=
      ⟨by rw [c_sp]; congr 1; omega, c14, cfs, cx, cdf, hrg,
        by rw [show (s.regs 4).toNat - 0x388 + 0x318 = (s.regs 4).toNat - 0x70 by omega]; exact q0,
        by rw [show (s.regs 4).toNat - 0x388 + 0x320 = (s.regs 4).toNat - 0x68 by omega]; exact q1,
        by rw [show (s.regs 4).toNat - 0x388 + 0x330 = (s.regs 4).toNat - 0x58 by omega]; exact q2,
        by rw [show (s.regs 4).toNat - 0x388 + 0x338 = (s.regs 4).toNat - 0x50 by omega]; exact q3,
        by rw [show (s.regs 4).toNat - 0x388 + 0x340 = (s.regs 4).toNat - 0x48 by omega]; exact q4⟩
    have hE := epre4 hPA hK hFw hAt
    have hS := hypSumO hap w_sub (by simp [numIntRegs]) (ExpW4.ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF
      hDiv hnsD hnsW4 b L (K - 0x78) (by omega) costD zp zl zc st xp xl xc yp ylen mp n mc)
    rw [show segAddr Extracted.program W4Loop.fn = 6205536 by decide] at hS
    have el : stLen S.mem st = stLen s.mem st := hrd (by unfold Apart at hstw ⊢; omega) hF
    have ev : natVal S.mem mp n = natVal s.mem mp n := hrd hPA.2.2.2.2.2.2.2.2.1.2.1 hF
    refine Reaches.call_regions (hS.withExit hret) c_pc ⟨?_, cx.trans h_x15, ?_, cdf.trans h_df, ?_⟩
      (fun s' hr ⟨⟨e4, e5, e14, ex15⟩, hq⟩ hrg' => ?_)
    · rw [hSsp, q_ra]; exact ra_of hap 0x77 (by decide)
    · simp [ArgsFrom64, argReg, intArgRegs, c0, c3, c1, c7, c6, c8, c9, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6]
    · unfold ExpW4.PreD
      rw [hSsp, c14, cfs, el, ev, show (s.regs 4).toNat - 0x78 - 0x388 = (s.regs 4).toNat - 0x388 - 0x78 by omega]
      unfold OBud at hB; rw [if_pos hy] at hB
      exact ⟨hE, hstnz, hMo, hM1, hB.1, hB.2⟩
    obtain ⟨hfs', hdf', hq'⟩ := hq
    have hq'' := hq'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMF, -⟩ := hq''
    have hk := slot_keep hPA hzA hc0 hF hSsp (show K - 0x78 + 0x390 = K + 0x318 by omega)
    have hs'sp : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x70) := by
      rw [e4]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, hSsp, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    refine epi impl ret hret _ (s.regs 4).toNat (s.regs 5).toNat 6205367 (Or.inl rfl) (by omega) (by omega) s'
      (by rw [hMF.accessible, hF.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)))
      (by rw [hr, retAddrOf, hSsp, q_ra]) hs'sp
      (by rw [hMF.readLE ((s.regs 4).toNat - 8) 8 (hk.of_sub (by omega) (by omega))]; exact q_bp)
      (by rw [hMF.readLE (s.regs 4).toNat 8 (hk.of_sub (by omega) (by omega)),
            hF.readLE (s.regs 4).toNat 8 (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact h_ret)
      fun s4 m4 k4 k0 k3 k1 k5 k14 kfs kdf kx => ?_
    exact ⟨⟨add8 rfl k4 (Nat.lt_of_le_of_lt ht48 (by decide)), k5.trans (ofNat_self _), k14.trans (e14.trans c14), kx.trans (ex15.trans cx)⟩,
      kfs.trans (hfs'.trans cfs), kdf.trans (hdf'.trans cdf),
      post_gen hPA hF hSsp (by omega) c14 (Or.inr (by unfold OCost; rw [if_pos hy])) hq' k0 k3 k1 m4⟩
  case K2 =>
    intro hy S M' c_pc c_sp c0 c3 c1 c7 c6 c8 c9 c14 cfs cdf cx cm hF hrg q_ra q_bp q0 q1 q2 q3 q4
    subst cm
    have hFw : MemFrame s.mem S.mem [((s.regs 4).toNat - 0x388 - 8 - K, (s.regs 4).toNat - 0x388 + 0x3f8)] :=
      hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
    have hSsp : (S.regs 4).toNat = (s.regs 4).toNat - 0x78 := by rw [c_sp]; exact tN (by omega)
    have hAt : AtCall ((s.regs 4).toNat - 0x388) yp ylen mp n mc s S :=
      ⟨by rw [c_sp]; congr 1; omega, c14, cfs, cx, cdf, hrg,
        by rw [show (s.regs 4).toNat - 0x388 + 0x318 = (s.regs 4).toNat - 0x70 by omega]; exact q0,
        by rw [show (s.regs 4).toNat - 0x388 + 0x320 = (s.regs 4).toNat - 0x68 by omega]; exact q1,
        by rw [show (s.regs 4).toNat - 0x388 + 0x330 = (s.regs 4).toNat - 0x58 by omega]; exact q2,
        by rw [show (s.regs 4).toNat - 0x388 + 0x338 = (s.regs 4).toNat - 0x50 by omega]; exact q3,
        by rw [show (s.regs 4).toNat - 0x388 + 0x340 = (s.regs 4).toNat - 0x48 by omega]; exact q4⟩
    have hE := epre2 hPA hK hK2 hFw hAt
    have hS := hypSumO hap w_sub (by simp [numIntRegs]) (ExpW2.ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF
      hDiv hnsD hnsW2 b L (K + 0xa0) (by omega) costD zp zl zc st xp xl xc yp ylen mp n mc)
    rw [show segAddr Extracted.program W2Loop.fn = 6210560 by decide] at hS
    have el : stLen S.mem st = stLen s.mem st := hrd (by unfold Apart at hstw ⊢; omega) hF
    have ev : natVal S.mem mp n = natVal s.mem mp n := hrd hPA.2.2.2.2.2.2.2.2.1.2.1 hF
    refine Reaches.call_regions (hS.withExit hret) c_pc ⟨?_, cx.trans h_x15, ?_, cdf.trans h_df, ?_⟩
      (fun s' hr ⟨⟨e4, e5, e14, ex15⟩, hq⟩ hrg' => ?_)
    · rw [hSsp, q_ra]; exact ra_of hap 0xc5 (by decide)
    · simp [ArgsFrom64, argReg, intArgRegs, c0, c3, c1, c7, c6, c8, c9, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6]
    · unfold ExpW2.PreD
      rw [hSsp, c14, cfs, el, ev, show (s.regs 4).toNat - 0x78 - 0x270 = (s.regs 4).toNat - 0x388 + 0xa0 by omega]
      unfold OBud at hB; rw [if_neg (by omega)] at hB
      exact ⟨hE, hstnz, hMo, hM1, hB.1, hB.2⟩
    obtain ⟨hfs', hdf', hq'⟩ := hq
    have hq'' := hq'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMF, -⟩ := hq''
    have hk := slot_keep hPA hzA hc0 hF hSsp (show K + 0xa0 + 0x278 = K + 0x318 by omega)
    have hs'sp : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x70) := by
      rw [e4]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, hSsp, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    refine epi impl ret hret _ (s.regs 4).toNat (s.regs 5).toNat 6205445 (Or.inr rfl) (by omega) (by omega) s'
      (by rw [hMF.accessible, hF.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)))
      (by rw [hr, retAddrOf, hSsp, q_ra]) hs'sp
      (by rw [hMF.readLE ((s.regs 4).toNat - 8) 8 (hk.of_sub (by omega) (by omega))]; exact q_bp)
      (by rw [hMF.readLE (s.regs 4).toNat 8 (hk.of_sub (by omega) (by omega)),
            hF.readLE (s.regs 4).toNat 8 (by simp only [pw, outside_cons, outside_nil, and_true]; omega)]; exact h_ret)
      fun s4 m4 k4 k0 k3 k1 k5 k14 kfs kdf kx => ?_
    exact ⟨⟨add8 rfl k4 (Nat.lt_of_le_of_lt ht48 (by decide)), k5.trans (ofNat_self _), k14.trans (e14.trans c14), kx.trans (ex15.trans cx)⟩,
      kfs.trans (hfs'.trans cfs), kdf.trans (hdf'.trans cdf),
      post_gen hPA hF hSsp (by omega) c14 (Or.inr (by unfold OCost; rw [if_neg (by omega)])) hq' k0 k3 k1 m4⟩

end FvModexp.Amd64.ExpOdd
