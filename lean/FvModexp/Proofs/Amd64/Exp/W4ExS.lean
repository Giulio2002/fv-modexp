import FvModexp.Proofs.Amd64.Exp.W4ExT
import FvModexp.Proofs.Amd64.Exp.CallW
import FvModexp.Proofs.Amd64.Nat.NatSub

set_option autoImplicit false

/-!
# window-4 (amd64), the subtract path of the final reduction (nat.go:1484-1488; agent expmc s47)

Twin of `Arm64.W4Loop.exSub`. At `nat.sub`'s entry (`W4Loop.exCmp`'s `KGe` state) with `zz = m` (the first
`zz.cmp(m) ≥ 0` and `zz ≤ m`, `ExpFinal.mont_one_le`): the call `zz = zz.sub(zz, m)` (divmc's `NatSub.ensR`, a summary
of the window layer's program `LibW`; its precondition's `CallEnv` from the loop's `Env` + `DataLoaded` at the anchor,
carried along the loop's frame), then `exSubT` (spills, the second `zz.cmp(m)` = `-1`, the join). The difference is `0`
of length `0`; `z`'s array is reused (`len zz = n ≤ cap zz`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Loop

theorem norm_zero {m : Memory} {p l : Nat} (hv : natVal m p l = 0) (hn : NatNorm m p l) : l = 0 := by
  rcases hn with h | h
  · exact h
  rcases l with _ | l
  · rfl
  exfalso; apply h
  rw [Nat.add_sub_cancel]
  unfold natVal at hv
  rw [show 8 * (l + 1) = 8 * l + 8 by omega, Arm64.Memory.readLE_add] at hv
  have h2 : 256 ^ (8 * l) * m.readLE (p + 8 * l) 8 = 0 := by omega
  rcases Nat.mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by decide)))
  · exact h3

/-- the top limb of an `n`-limb value -/
theorem top_limb (m : Memory) (p n : Nat) (hn : 0 < n) :
    m.readLE (p + 8 * (n - 1)) 8 = m.readLE p (8 * n) / 256 ^ (8 * (n - 1)) := by
  have e : 8 * n = 8 * (n - 1) + 8 := by omega
  rw [e, Arm64.Memory.readLE_add]
  have hlt := Arm64.Memory.readLE_lt m p (8 * (n - 1))
  have hpos : 0 < 256 ^ (8 * (n - 1)) := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem norm_of_eq {m m' : Memory} {p q n : Nat} (h : m.readLE p (8 * n) = m'.readLE q (8 * n))
    (hq : NatNorm m' q n) : NatNorm m p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · exact Or.inl h0
  rcases hq with h0 | h1
  · exact Or.inl h0
  · right
    rw [top_limb m p n hn, h, ← top_limb m' q n hn]; exact h1

/-- the loop's environment as the callee environment `CEnv` of a call at `RSP = sp - 8` (window = the whole frame) -/
theorem Env.cenv {R : RtInv} {L : List (Nat × Nat)} {g fs sp : Nat} {M0 : Memory} (he : Env R L g fs sp M0)
    (hd : Extracted.program.DataLoaded M0) (hro : RoOut R) : CallW.CEnv R L g fs (sp - 8) 4288 968 M0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := he
  have e1 : sp - 8 - 4288 = sp - 4296 := by omega
  have e2 : sp - 8 + 968 = sp + 0x3c0 := by omega
  unfold CallW.CEnv
  rw [e1, e2]
  exact ⟨by omega, by omega, by omega, h4, h5, h6, by omega, h8, h9, h10, h11, hd, hro, h12.1, h12.2, h13, h14, h16,
    h15⟩

/-- `CEnv` at a loop state (memory `M`, frame `FL` since the anchor) -/
theorem Env.cenvM {R : RtInv} {L : List (Nat × Nat)} {g fs sp : Nat} {M0 M : Memory} {zp zc zzp zzc : Nat}
    (he : Env R L g fs sp M0) (hd : Extracted.program.DataLoaded M0) (hro : RoOut R)
    (hF : FL R L sp zp zc zzp zzc M0 M) (hrg : M.regions = M0.regions)
    (hz : M0.accessible zp (8 * zc) true = true) (hzz : M0.accessible zzp (8 * zzc) true = true)
    (hgz : Apart (g + 16) 8 zp (8 * zc)) (hgzz : Apart (g + 16) 8 zzp (8 * zzc))
    (hfz : Apart (fs - 8) 8 zp (8 * zc)) (hfzz : Apart (fs - 8) 8 zzp (8 * zzc)) :
    CallW.CEnv R L g fs (sp - 8) 4288 968 M := by
  have hs1 : 4296 ≤ sp := he.2.1
  have hacc := he.2.2.2.1
  have hgw := he.2.2.2.2.2.2.2.2.1
  have hfw := he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine CallW.CEnv.frame (Env.cenv he hd hro) (ws := fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)])
    (by simpa only [lw, List.append_assoc] using hF.1) hrg ?_ ?_ ?_
  · intro r hr hlt
    simp only [fw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    all_goals first
      | exact M0.accessible_sub hacc (Or.inr rfl) (by dsimp only; omega) (by dsimp only; omega)
      | (dsimp only; rw [show zp + 8 * zc - zp = 8 * zc by omega]; exact hz)
      | (dsimp only; rw [show zzp + 8 * zzc - zzp = 8 * zzc by omega]; exact hzz)
  · unfold Apart at hgw hgz hgzz
    simp only [fw, outside_append, outside_cons, outside_nil, and_true]
    omega
  · unfold Apart at hfw hfz hfzz
    simp only [fw, outside_append, outside_cons, outside_nil, and_true]
    omega

theorem jw_sub {rt : List (Nat × Nat)} {sp p c a k : Nat} (hs : 4296 ≤ sp)
    (ho : Outside a k (rt ++ [(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x188, sp + 0x190)] ++
      [(p, p + 8 * c)])) :
    Outside a k (rt ++ [(sp - 8 - 4288, sp - 8 + 80)] ++ [(p, p + 8 * c)]) ∧ Outside a k (tw sp) := by
  simp only [tw, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
  obtain ⟨⟨h1, h2⟩, h5⟩ := ho
  exact ⟨⟨⟨h1, by omega⟩, h5⟩, h2⟩

theorem tw_of_live {L : List (Nat × Nat)} {sp a k : Nat} (hLs : LiveSep L [(sp - 4296, sp + 0x3c0)])
    (hs : 4296 ≤ sp) (hin : InRanges a k L) : Outside a k (tw sp) := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := hLs r hr
  simp only [tw, outside_cons, outside_nil, and_true] at this ⊢
  omega

theorem subNames : ∀ x, NatSub.names.contains x = true → LibW.names.contains x = true :=
  MontW.sub_of_all (by decide)

theorem sub_not : NatSub.names.contains fn = false := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the subtract path, from `nat.sub`'s entry (`zz = m`) to the join -/
theorem exSub {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory} (hd : Extracted.program.DataLoaded M0)
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) {ret : W64} {Q : State → Prop}
    (S : State) (r5 : W64) (zp zc zzp zzc : Nat)
    (hpc : S.rip = BitVec.ofNat 64 subE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hra : S.mem.readLE (sp - 8) 8 = fnE + 0x1130) (h5 : S.regs 5 = r5)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h1 : S.regs 1 = BitVec.ofNat 64 zzc)
    (h7 : S.regs 7 = BitVec.ofNat 64 zzp) (h6 : S.regs 6 = BitVec.ofNat 64 n) (h8 : S.regs 8 = BitVec.ofNat 64 zzc)
    (h9 : S.regs 9 = BitVec.ofNat 64 mp) (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = BitVec.ofNat 64 mc)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (hz8 : zzp % 8 = 0) (hnm : NatNorm M0 mp n) (heq : S.mem.readLE zzp (8 * n) = M0.readLE mp (8 * n))
    (KJ : ∀ (S' : State) (p l c : Nat), S'.rip = BitVec.ofNat 64 njoin → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
      JoinPost R b L g sp n zzp zzc 0 S.mem p l c S'.mem → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hst.1
  have hs1 : 4296 ≤ sp := he.2.1; have hs2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  have hrt := he.2.2.2.2.2.2.2.1
  have hLs := he.2.2.2.2.2.2.2.2.2.2.1
  have hn := hst.2.1; have hn16 := hst.2.2.1; have hmc := hst.2.2.2.1; have hmc' := hst.2.2.2.2.1
  have hm := hst.2.2.2.2.2.2.2.2.1
  have hB0 := hB
  obtain ⟨hBz, hBzz, -, hzm, hzzm, -, -, -, -⟩ := hB
  obtain ⟨hzc1, hzc2, hza, hzb, hzh, hzw, hzg, hzf⟩ := hBz
  obtain ⟨hzzc1, hzzc2, hzza, hzzb, hzzh, hzzw, hzzg, hzzf⟩ := hBzz
  obtain ⟨hma, hmb, hmh, hmw⟩ := hm
  have hFL := hM.1
  have hmS : S.mem.readLE mp (8 * n) = M0.readLE mp (8 * n) := FL.read hFL hmh hmw hs1 hzm hzzm
  -- the callee environment
  have hce := Env.cenvM he hd hro hFL hM.2.2 hza hzza hzg hzzg hzf hzzf
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tg : (S.regs 14).toNat = g := by rw [h14]; exact MontW.toNat_of (by omega)
  have hcall := CallW.callEnv_of (CallW.CEnv.mono hce (Nat.le_refl 4288) (show 80 ≤ 968 by omega)) tsp tg hfs rfl
    (stk := 4288) (above := 80) (Nat.le_refl _) (by omega) (by omega)
  -- the summary
  have hS := Ensures.toSummaryIn (NatSub.ensR impl hap R hmk hmv b L (BitVec.ofNat 64 zzp) (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 zzc) (BitVec.ofNat 64 zzp) (BitVec.ofNat 64 n) (BitVec.ofNat 64 zzc) (BitVec.ofNat 64 mp)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc))
    (A64.noExit_restrict64 hap NatSub.names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap subNames)
  rw [← LibW.eq_only, show segAddr Extracted.program NatSub.fn = 6183136 by decide] at hS
  have tz := MontW.toNat_of (x := zzp) (by omega)
  have tn := MontW.toNat_of (x := n) (by omega)
  have tzc := MontW.toNat_of (x := zzc) (by omega)
  have tm := MontW.toNat_of (x := mp) (by omega)
  have tmc := MontW.toNat_of (x := mc) (by omega)
  have u1 := hzzw; have u2 := hmw; have u3 := hzzg; have u4 := hzzf; have u5 := hzzm
  unfold Apart at u1 u2 u3 u4 u5
  refine ReachesRet.call_regions hS hpc ⟨?ra, hx15, ?args, hdf, ?pre⟩
    (fun s' hr ⟨⟨e4, e5, e14, ex15⟩, hq, hr1, hr2⟩ hrg => ?_)
  case ra =>
    rw [tsp, hra, fnE_eq]; exact ra_of hap sub_not 0x1130 (by decide)
  case args =>
    simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  case pre =>
    unfold NatSub.Pre NatSub.PreS
    rw [tz, tn, tzc, tm, tmc]
    simp only [win, tsp, tg, hfs]
    refine ⟨hcall, hwt, Nat.le_refl _, ?_, by omega, hmc, by omega, by omega, by omega, by omega, by omega,
      fun _ => ⟨hz8, hzzh, by rw [hM.1.1.accessible]; exact hzza, hzzb⟩, ?_, fun _ => ⟨?_, ?_, Or.inl trivial, ?_⟩,
      ?_, by omega, Held.sub (R := R) hzzh (Nat.le_refl _) (by omega), ?_, ?_, ?_, by rw [hM.1.1.accessible]; exact hma, hmb, hmh,
      ?_, hM.2.1, fun h => absurd h (by omega), fun d src k hk => hmvok d src k (by omega)⟩
    · simp only [natVal]; rw [heq, hmS]; exact Nat.le_refl _
    all_goals try (simp only [outside_cons, outside_nil, and_true]; omega)
    · unfold Apart; omega
    · unfold Apart; omega
    · exact Or.inr (by unfold Apart; omega)
    · rw [hM.1.1.accessible]
      exact M0.accessible_sub hzza (Or.inr rfl) (Nat.le_refl _) (by omega)
    · exact norm_of_eq heq hnm
    · exact norm_of_eq hmS hnm
  -- after `nat.sub`
  obtain ⟨hfs', hdf', p', n', c', q0, q3, q1, hval, hnorm, hlc, hln, L', b', hLE, hb', hinv', hlive, hor, hF, hLF⟩ := hq
  simp only [tz, tn, tzc, tm] at hval hr1 hF hLF hb'
  simp only [win, tsp, tg] at hF hinv'
  obtain ⟨ep, ec⟩ := hr1 (by omega)
  rw [q0] at ep; rw [q1] at ec
  subst ep ec
  have hl0 : n' = 0 := norm_zero (by rw [hval]; simp only [natVal]; rw [heq, hmS, Nat.sub_self]) hnorm
  subst hl0
  have hc : MemFrame S.mem s'.mem (R.rt ++ [(sp - 8 - 4288, sp - 8 + 104)] ++ [(p', p' + 8 * c')]) :=
    hF.mono fun a k ho => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨ho.1.1, by omega⟩, ho.2⟩
  have hFL' : FL R L sp zp zc p' c' M0 s'.mem := FL.call hFL hc hLF (Or.inr ⟨rfl, rfl⟩) hs1
  obtain ⟨q3a8, q3b0, q3b8, -, -, -⟩ := Static.rd hst hFL' hB0.1 hB0.2.1
  have hpc' : s'.rip = BitVec.ofNat 64 (fnE + 0x1130) := by rw [hr, retAddrOf_eq, tsp, hra]
  have hsp' : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, hsp]; exact sp_add8 (by omega) (by omega)
  have hacc' : s'.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
    rw [hF.accessible, hM.1.1.accessible]; exact he.2.2.2.1
  have hma' : s'.mem.accessible mp (8 * n) false = true := by
    rw [hF.accessible, hM.1.1.accessible]; exact hma
  refine exSubT hap s' sp g fs p' c' mp n mc r5 hpc' hsp' (e5.trans h5) (e14.trans h14) (by rw [hfs', hfs])
    (ex15.trans hx15) (hdf'.trans hdf) (by rw [← q0, Expmc.bv_ofNat_toNat]) (by rw [← q3, Expmc.bv_ofNat_toNat])
    (by rw [← q1, Expmc.bv_ofNat_toNat]) q3a8 q3b0 q3b8 (by omega) (by omega) hs1 hs2 hacc' hn hn16 hmb hma' hmw ?_
  intro S4 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hW hrg4
  have hWR : ∀ r ∈ tw sp, InRanges r.1 (r.2 - r.1) L' ∨ Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [tw, List.mem_cons, List.not_mem_nil, or_false] at hr
    right
    rcases hr with rfl | rfl | rfl <;> exact hrt.of_sub (by dsimp only; omega) (by dsimp only; omega)
  refine KJ S4 p' 0 c' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⟨L', b', hLE, hb', FvModexp.Expmc.inv_frame hW hWR hinv',
    by rw [hrg4, hrg], ?_, ?_, by simp [natVal], by omega, ⟨by omega, by omega⟩, ?_, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
  · exact hF.trans hW (fun a k ho => jw_sub hs1 ho)
  · exact hLF.trans (FvModexp.Expmc.liveFrame_of_frame hW (fun a k hin _ => tw_of_live hLs hs1 hin))
      (fun _ _ h => h)
  · intro hc0
    obtain ⟨w1, w2, w3, w4⟩ := hlive hc0
    exact ⟨w1, w2, by rw [hW.accessible]; exact w3, w4⟩

end FvModexp.Amd64.W4Loop
