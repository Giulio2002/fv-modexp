import FvModexp.Proofs.Amd64.Int.QRA
import FvModexp.Proofs.Amd64.Int.QRP
import FvModexp.Proofs.Amd64.Int.QRPost
import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64) as `(*Int).Mod` calls it: `QRSpec` (`qr_ens`)

Composition: segment A (`runQA`: entry → `nat.div`'s entry; `nat.div`'s precondition by `divPre_of`), the call of
`nat.div` (premise `DivHypM`, an `Ensures` on `onlySegments nsD`, moved to `LibQR` by `Ensures.toSummaryIn`), segment
B (`runQB`: `q`'s header, `gcWriteBarrier4`, `z`'s header, `RET`) and `atD_of` / `post_of`. Twin of the arm64
`IMod.ens` (Arm64/Int/ModFun.lean, where `QuoRem` is inlined into `Mod`).
`pairwise_ne`, `find_none_of`, `retAddr_restrict`: copied from agent infra's `Amd64/Exp/CallW.lean` (so that this chain
does not import `LibExp`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IMod

open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe maxW ModBudget lenW)

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hR _ _ (hp.1 a ha')
      · exact pairwise_ne hR hp.2 ha' hb' hne

theorem find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact find_none_of h x hx'

/-- A return address inside the code of a segment `cs` of `P` whose name is not in `ns` is a `RetAddr` of the
restricted program of `ns` (amd64). -/
theorem retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
    {ns : List String} {cs : Amd64.Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat)
    (hi : i < cs.bytes.length) (hu : cs.base + i < 2 ^ 47) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + i) := by
  refine ⟨hu, fun seg hseg => ?_, fun st hst => ?_⟩
  · have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have hne : seg ≠ cs := by
      rintro rfl
      rcases List.mem_append.1 hseg with h | h
      · have := (List.mem_filter.1 h).2
        rw [hn] at this; exact absurd this (by decide)
      · have := hap.1
        rw [List.pairwise_append] at this
        have := this.2.2 seg hcs seg h
        unfold Amd64.Segment.Apart at this
        omega
    have := pairwise_ne (fun a b h => by unfold Amd64.Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Amd64.Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Amd64.Program.stubAt at h1
    have := find_none_of h1 st hst
    simp at this
    exact this

set_option maxRecDepth 20000 in
/-- the return address of the `nat.div` call (`QuoRem+0x8c`) is outside any program without `QuoRem` -/
theorem raD_ret (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains Extracted.seg6.name = false) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) raD := by
  have := retAddr_restrict hap (cs := Extracted.seg6)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn 0x8c
    (by decide) (by decide)
  rwa [show Extracted.seg6.base + 0x8c = raD by decide] at this

/-- an opaque wrapper: `omega` does not case-split on a boxed disjunction -/
structure Box (P : Prop) : Prop where
  unbox : P

theorem bv_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem bv_mod (n : Nat) : BitVec.ofNat 64 n = BitVec.ofNat 64 (n % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`q.QuoRem(z, y, z)`** (amd64) as `(*Int).Mod` calls it (`QRSpec`). Premises: `nat.div` as `QuoRem` calls it
(`DivHypM`: `stk == nil`, `z2 = u`; on any program `nsD ⊆ LibQR.names` without `QuoRem`, window `stkD + 120 ≤ stk`,
`aboveD ≤ 112`), the 4-slot write barrier, the stack (the barrier's 4096 bytes below QuoRem's frame; `q`'s header in
the window above) and `div`'s cost within `ModBudget` for operands of at most 128 words. -/
theorem qr_ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {nsD : List String} {stkD aboveD : Nat} {cost : Nat → Nat → Nat}
    (hD : DivHypM impl R nsD stkD aboveD cost)
    (hnsD : ∀ x, nsD.contains x = true → LibQR.names.contains x = true)
    (hnsQ : nsD.contains Extracted.seg6.name = false)
    (hwb : WbLiveContract64 (LibQR.program.link impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    {stk above : Nat} (hstkD : stkD + 120 ≤ stk) (habD : aboveD ≤ 112) (h4224 : 4224 ≤ stk) (hab : 128 ≤ above)
    (hbud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → cost ul vl ≤ ModBudget (max ul vl)) :
    QRSpec impl R stk above := by
  intro b L q z y
  rw [← LibQR.eq_only, fnQ_eq]
  intro ret hret s hs hpre
  janus64_intro hs
  have hr48 := hret.user
  obtain ⟨hIP, hyv, hlz, hly, hpool, hX, hqA, hq8, hq16, hq24, hadx⟩ := hpre
  have hIP' := hIP
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hstk, hab48, hacc⟩, hal, -, hrt, -, -, hLs, -⟩, hsv, hG, -, -, hops, hpw⟩ := hIP'
  simp only [regSP, regG, stackguard0, stackguard0Offset] at hstk hab48 hacc hg1 hg2 hg3
  have hoz := hops z.toNat (by simp)
  have hoy := hops y.toNat (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hpw
  obtain ⟨⟨hzyH, -, -, -⟩, -⟩ := hpw
  obtain ⟨⟨hz0, -, hz48, hzacc, hzH, -, -, -, hzap, -⟩, hzW, hzO, -, -, -, -⟩ := hoz
  obtain ⟨⟨-, -, hy48, hyacc, hyH, -, -, -, -, -⟩, hyW, -, -, -, -, -⟩ := hoy
  have hok : R.ok (cA "runtime.gcWriteBarrier4") [4] := hsv.2.2.2.2.2.2.1 _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, hwbw⟩ := id hG
  generalize hzp : s.mem.readLE (z.toNat + 8) 8 = zp at hzap hzO
  generalize hzc : s.mem.readLE (z.toNat + 24) 8 = zc at hzap hzO
  generalize hzl : s.mem.readLE (z.toNat + 16) 8 = zl
  generalize hyp : s.mem.readLE (y.toNat + 8) 8 = yp
  generalize hyl : s.mem.readLE (y.toNat + 16) 8 = yl
  generalize hyc : s.mem.readLE (y.toNat + 24) 8 = yc
  have hzl128 : zl ≤ 128 := by have := hlz; simp only [IntLenLe, maxW] at this; rw [hzl] at this; exact this
  have hyl128 : yl ≤ 128 := by have := hly; simp only [IntLenLe, maxW] at this; rw [hyl] at this; exact this
  have hB : ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) = ModBudget (max zl yl) := by
    simp only [lenW]; rw [hzl, hyl]
  have hcost : cost zl yl ≤ ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) := by
    rw [hB]; exact hbud zl yl hzl128 hyl128
  generalize ht : (s.regs 4).toNat = t at hstk hab48 hacc hg3 hal hqA
  have hsp0 : s.regs 4 = BitVec.ofNat 64 t := by rw [← ht, Expmc.bv_ofNat_toNat]
  have hzS : z.toNat + 32 ≤ t - stk ∨ t + above ≤ z.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hzW; omega
  have hyS : y.toNat + 32 ≤ t - stk ∨ t + above ≤ y.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hyW; omega
  have hrtW : Outside (t - stk) (stk + above) R.rt := by rw [← ht]; exact hrt
  unfold Apart at hzyH
  -- segment A
  refine returns_of_reaches (runQA impl ret hret _ t (s.regs 14).toNat (s.regs 5).toNat q.toNat z.toNat y.toNat
    zp zl zc yp yl yc s.mem (BitVec.isLt _) (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) (Janus.Arm64.Memory.accessible_weaken _
      (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))) hg1 hg2 (by omega) hz48
    (Janus.Arm64.Memory.accessible_weaken _ hzacc) (by omega) hy48 (Janus.Arm64.Memory.accessible_weaken _ hyacc)
    (by omega) hqA (hqA ▸ hq8) (hqA ▸ hq16) (hqA ▸ hq24) hzp hzl hzc hyp hyl hyc
    s h_rip hsp0 (h_a0.trans (Expmc.bv_ofNat_toNat _).symm) (h_a1.trans (Expmc.bv_ofNat_toNat _).symm)
    (h_a2.trans (Expmc.bv_ofNat_toNat _).symm) (h_a3.trans (Expmc.bv_ofNat_toNat _).symm)
    (Expmc.bv_ofNat_toNat _).symm (Expmc.bv_ofNat_toNat _).symm rfl ?KA)
  intro S3 M3 c_pc c_sp c0 c3 c1 c7 c6 c8 c9 c14 c5 cfs cdf cx cm hF3 hrg3 r_ra r112 r104 r96 r88 r80 r72 rbp
    r8 r16 r24 r32
  subst cm
  have hsp3 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by rw [c_sp, BitVec.toNat_ofNat, ht]; omega
  have e8 : (S3.regs 4).toNat + 8 = t - 112 := by rw [hsp3, ht]; omega
  have e16 : (S3.regs 4).toNat + 16 = t - 104 := by rw [hsp3, ht]; omega
  have e24 : (S3.regs 4).toNat + 24 = t - 96 := by rw [hsp3, ht]; omega
  have e32 : (S3.regs 4).toNat + 32 = t - 88 := by rw [hsp3, ht]; omega
  have e40 : (S3.regs 4).toNat + 40 = t - 80 := by rw [hsp3, ht]; omega
  have e48 : (S3.regs 4).toNat + 48 = t - 72 := by rw [hsp3, ht]; omega
  have hF3' : MemFrame s.mem S3.mem [((s.regs 4).toNat - 120, (s.regs 4).toNat - 64),
      ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 40)] := by
    rw [ht]; exact hF3
  have hP := divPre_of (cost := cost) hIP hyv hpool hX hadx hstkD habD (by omega) hzp hzl hzc hyp hyl hyc hzl128
    hyl128 hcost hsp3 c14 cfs hrg3 hF3' (by rw [e8]; exact r112) (by rw [e16]; exact r104) (by rw [e24]; exact r96)
    (by rw [e32]; exact r88) (by rw [e40]; exact r80) (by rw [e48]; exact r72)
  -- the call of `nat.div`
  have hzp64 : zp < 2 ^ 64 := hzp ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzl64 : zl < 2 ^ 64 := hzl ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc64 : zc < 2 ^ 64 := hzc ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hS := Ensures.toSummaryIn (hD b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc) yp yl yc)
    (A64.noExit_restrict64 hap nsD) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hnsD)
  rw [← LibQR.eq_only, fnD_eq] at hS
  simp only [bv_toNat hzp64, bv_toNat hzl64, bv_toNat hzc64] at hS
  refine Reaches.call_regions (hS.withExit hret) c_pc ⟨?_, cx.trans h_x15, ?_, cdf.trans h_df, hP⟩
    fun S4 hpc4 hq hrg4 => ?_
  · rw [c_sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), r_ra]; exact raD_ret impl hap hnsQ
  · simp [ArgsFrom64, argReg, intArgRegs, c0, c3, c1, c7, c6, c8, c9]
  obtain ⟨⟨sp4, rbp4, r14_4, x15_4⟩, hfs4, hdf4, qq, ql, qc, r, rl, rc, e0, e3, e1, e7, e6, e8', L', b', hr, hrt',
    hMF, hLF⟩ := hq
  have hx := hrt'.1
  have hS4 : (S4.regs 4).toNat = t - 112 := by
    have ht48 : t + 128 ≤ 2 ^ 48 := by omega
    have e : (S4.regs 4).toNat = ((S3.regs 4).toNat + 8) % 2 ^ 64 := by rw [sp4, BitVec.toNat_add]; rfl
    rw [e, hsp3, ht, Nat.mod_eq_of_lt (by omega)]; omega
  have hz' : 0 < zc → zp + 8 * zc ≤ t - stk ∨ t + above ≤ zp := fun h => by
    have := hzO h; simp only [win, ht, outside_cons, outside_nil, and_true] at this; exact this
  -- what `div` keeps: its frame misses `[t - 8, t + 40)`
  have hslot : ∀ a k, t - 8 ≤ a → a + k ≤ t + 40 → S4.mem.readLE a k = S3.mem.readLE a k := by
    intro a k h1 h2
    refine Janus.Arm64.Memory.readLE_congr fun i hi => FvModexp.ByteFrame.MemFrame.byte hMF ?_
    rw [outside_append, outside_append]
    refine ⟨⟨hrtW.of_sub (by omega) (by omega), ?_⟩, ?_⟩
    · simp only [win, hsp3, ht, outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]
      rcases Nat.eq_zero_or_pos zc with h0 | h0
      · subst h0; omega
      · have := hz' h0; omega
  have s8 : S4.mem.readLE (t + 8) 8 = q.toNat := by rw [hslot _ _ (by omega) (by omega)]; exact r8
  have s16 : S4.mem.readLE (t + 16) 8 = z.toNat := by rw [hslot _ _ (by omega) (by omega)]; exact r16
  have s24 : S4.mem.readLE (t + 24) 8 = y.toNat := by rw [hslot _ _ (by omega) (by omega)]; exact r24
  have s32 : S4.mem.readLE (t + 32) 8 = z.toNat := by rw [hslot _ _ (by omega) (by omega)]; exact r32
  have sbp : S4.mem.readLE (t - 8) 8 = (s.regs 5).toNat := by rw [hslot _ _ (by omega) (by omega)]; exact rbp
  have sra : S4.mem.readLE t 8 = ret := by
    rw [hslot _ _ (by omega) (by omega), hF3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      ← ht]
    exact h_ret
  have hzS4 : z.toNat + 32 ≤ t - 4224 ∨ t + 128 ≤ z.toNat := by
    clear hyS hzyH; rcases hzS with h | h <;> omega
  have hyS4 : y.toNat + 32 ≤ t - 4224 ∨ t + 128 ≤ y.toNat := by
    clear hzS hzyH; rcases hyS with h | h <;> omega
  have bzS := Box.mk hzS4
  have byS := Box.mk hyS4
  have bzy := Box.mk hzyH
  have bzW := Box.mk hzS
  clear hzS hyS hzyH hzS4 hyS4
  -- `z`'s header (neg byte) is kept by `div`
  have hzb : ∀ i, i < 32 → S4.mem.bytes (z.toNat + i) = s.mem.bytes (z.toNat + i) := by
    intro i hi
    have hZ : Outside (z.toNat + i) 1 [(zp, zp + 8 * zc)] := by
      simp only [outside_cons, outside_nil, and_true]
      rcases Nat.eq_zero_or_pos zc with h0 | h0
      · subst h0; omega
      · have := hzap h0; unfold Apart at this; omega
    have e3' : S3.mem.bytes (z.toNat + i) = s.mem.bytes (z.toNat + i) :=
      FvModexp.ByteFrame.MemFrame.byte hF3 (by
        have := bzS.unbox; simp only [outside_cons, outside_nil, and_true]; omega)
    rw [← e3']
    rcases hzH with hi' | ho
    · exact FvModexp.ByteFrame.LiveFrame.byte hLF (hi'.sub (by omega) (by omega)) hZ
    · refine FvModexp.ByteFrame.MemFrame.byte hMF ?_
      rw [outside_append, outside_append]
      refine ⟨⟨ho.of_sub (by omega) (by omega), ?_⟩, hZ⟩
      have := bzW.unbox; simp only [win, hsp3, ht, outside_cons, outside_nil, and_true]; omega
  have hng : S4.mem.readLE z.toNat 1 = 0 := by
    rw [Janus.Arm64.Memory.readLE_congr (m' := s.mem) fun i hi => by have := hzb i (by omega); exact this]
    exact hz0
  have hr64 : r < 2 ^ 64 := by
    obtain ⟨-, -, -, -, hnl, hd⟩ := hr
    rcases Nat.eq_zero_or_pos rc with h0 | h0
    · rcases hd with ⟨rfl, -⟩ | ⟨h1, -⟩
      · exact hzp64
      · omega
    · have := (hnl h0).2.2.2; omega
  have hrc40 : rc < 2 ^ 40 := hr.2.2.2.1
  have hrlc : rl ≤ rc := hr.2.2.1
  have hacc4 : ∀ a k w, S4.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hMF.accessible, hF3.accessible]
  have hLs4 : LiveSep L' [(t - 4224, t + 128)] := by
    refine hx.liveSep (fun r hr => ?_) (fun r hr => ?_)
    · have := hLs r hr; simp only [win, ht, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hrtW.of_sub (by omega) (by omega)
  have hrt44 : Outside (t - 4224) (4224 + 128) R.rt := hrtW.of_sub (by omega) (by omega)
  have hinv4 : R.inv b' L' (S4.regs 14).toNat (view R.rt L' S4.mem) := by rw [r14_4]; exact hrt'.2.2
  -- segment B
  refine runQB impl R hwb ret hret _ t (s.regs 5).toNat q.toNat z.toNat y.toNat (qq % 2 ^ 64) (ql % 2 ^ 64)
    (qc % 2 ^ 64) r rl rc b' L' S4 hal (by omega) (by omega) hqA
    (by rw [hacc4]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hrt44 hLs4
    (by rw [hacc4]; exact hwbacc)
    (by simp only [win, ht, outside_cons, outside_nil, and_true] at hwbw; omega)
    hz48 (by rw [hacc4]; exact hzacc) bzS.unbox (hx.held hzH) hy48
    (by rw [hacc4]; exact Janus.Arm64.Memory.accessible_weaken _ hyacc) byS.unbox (hx.held hyH) bzy.unbox hok hinv4
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hr64 (by omega) (by omega)
    (by rw [hpc4, retAddrOf, c_sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), r_ra])
    (by rw [← Expmc.bv_ofNat_toNat (S4.regs 4), hS4])
    (e0.trans (bv_mod qq)) (e3.trans (bv_mod ql)) (e1.trans (bv_mod qc)) e7 e6 e8' s8 s16 s24 s32 sbp sra hng ?KF
  intro s4 Mw qn ql' rl' hm hql hrl hMw hLw hIw hsp4 h04 h144 h54 hfs4' hdf4' hx4
  subst hql hrl
  have hA := atD_of hIP h4224 hab hstkD habD hzp hzl hzc hyp hyl hcost hsp3 hF3' hr hrt' hMF hLF hr64
    (by rw [ht]; exact hqA) (by rw [ht]; exact hMw) hLw (by rw [r14_4, c14] at hIw; exact hIw)
  obtain ⟨hPost, hyv'⟩ := post_of hIP hab hA s4 (by rw [hm, hqA, ht])
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfs4'.trans (hfs4.trans cfs), hdf4'.trans (hdf4.trans cdf), h04, hPost, hyv'⟩
  · show s4.regs 4 = s.regs 4 + 8#64
    rw [hsp4, hsp0]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · show s4.regs 5 = s.regs 5
    rw [h54, Expmc.bv_ofNat_toNat]
  · show s4.regs 14 = s.regs 14
    rw [h144, r14_4, c14]
  · show s4.xmm 15 = s.xmm 15
    rw [hx4, x15_4, cx]

end FvModexp.Amd64.IMod
