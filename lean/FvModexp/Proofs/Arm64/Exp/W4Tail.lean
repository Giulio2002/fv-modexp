import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4ExitC

/-!
# window-4 (arm64), from the main loop's exit to the return (nat.go:1477-1490)

`exA` (`zz = zz.montgomery(z, one, …)`) → `exB` (final reduction, join) → `fin` (`zz.norm()`, deferred `stk.restore`,
return). The conclusion lists the facts of the three stages: `Mem` (anchor `M0` → memory `M'` at the first cmp),
`JoinPost` (`M'` → join memory `Mj`, value `if m ≤ zz then 0 else zz` with `zz = montgomery(z, 1)`), `FinPost`
(`Mj` → return).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

/-- a held range outside the written stack ranges and the two buffers reads at the join as at the anchor -/
theorem rd_chain {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zp zc zzp zzc V p l c a k : Nat}
    {M0 M' Mj : Memory} (hM : Mem R b L g sp M0 M' zp zc zzp zzc)
    (hJ : JoinPost R b L g sp n zzp zzc V M' p l c Mj) (hh : InRanges a k L ∨ Outside a k R.rt)
    (h1 : Outside a k (fw sp))
    (h2 : Outside a k [(sp - 4304, sp - 8), (sp + 8, sp + 80), (sp + 160, sp + 176), (sp + 400, sp + 408)])
    (hz : Outside a k [(zp, zp + 8 * zc)]) (hzz : Outside a k [(zzp, zzp + 8 * zzc)]) :
    Mj.readLE a k = M0.readLE a k := by
  obtain ⟨hF, hLF, _, _⟩ := hM
  obtain ⟨_, _, _, _, _, _, hF2, hLF2, _⟩ := hJ
  rw [FvModexp.Expmc.held_readLE hh hF2 hLF2 h2 hzz]
  refine FvModexp.Expmc.held_readLE hh hF hLF h1 ?_
  simp only [outside_cons, outside_nil, and_true] at hz hzz ⊢
  exact ⟨hz, hzz⟩

theorem acc_chain {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zp zc zzp zzc V p l c : Nat}
    {M0 M' Mj : Memory} (hM : Mem R b L g sp M0 M' zp zc zzp zzc)
    (hJ : JoinPost R b L g sp n zzp zzc V M' p l c Mj) (a k : Nat) (w : Bool) :
    Mj.accessible a k w = M0.accessible a k w := by
  obtain ⟨hF, _, _, _⟩ := hM
  obtain ⟨_, _, _, _, _, _, hF2, _, _⟩ := hJ
  rw [hF2.accessible, hF.accessible]

/-- the join's `FinEnv` from the anchor's -/
theorem finEnv_chain {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zp zc zzp zzc V p l c st n0 ret : Nat}
    {r29 : BitVec 64} {M0 M' Mj : Memory} (hM : Mem R b L g sp M0 M' zp zc zzp zzc)
    (hJ : JoinPost R b L g sp n zzp zzc V M' p l c Mj) (he : FinEnv sp g st n0 r29 ret M0)
    (hwrt : Outside (sp - 4288) (4288 + 1040) R.rt) (hgrt : Outside (g + 16) 8 R.rt)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstz : Apart zp (8 * zc) st 24) (hstzz : Apart zzp (8 * zzc) st 24)
    (hgz : Apart (g + 16) 8 zp (8 * zc)) (hgzz : Apart (g + 16) 8 zzp (8 * zzc))
    (hsz : Apart zp (8 * zc) (sp - 4288) (4288 + 1040)) (hszz : Apart zzp (8 * zzc) (sp - 4288) (4288 + 1040))
    (hgw4 : Apart (g + 16) 8 (sp - 4304) (4304 + 1040)) (hstw4 : Apart st 24 (sp - 4304) (4304 + 1040)) :
    FinEnv sp g st n0 r29 ret Mj := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r912, r840, r848, r856, hst1, hst2, hn0, hstw, hstg, rfp, rlr⟩ := he
  unfold Apart at hstz hstzz hgz hgzz hsz hszz hstw hgw hgw4 hstw4
  have slot : ∀ a, (sp - 8 ≤ a ∧ a + 8 ≤ sp + 8) ∨ (sp + 832 ≤ a ∧ a + 8 ≤ sp + 864) ∨ a = sp + 912 →
      Mj.readLE a 8 = M0.readLE a 8 := by
    intro a ha
    refine rd_chain hM hJ (Or.inr (hwrt.of_sub (by omega) (by omega))) ?_ ?_ ?_ ?_ <;>
      simp only [fw, outside_cons, outside_nil, and_true] <;> omega
  have stR : ∀ a k, st ≤ a → a + k ≤ st + 24 → Mj.readLE a k = M0.readLE a k := by
    intro a k h1 h2
    refine rd_chain hM hJ (hsth.imp (fun h => h.sub h1 h2) (fun h => h.of_sub h1 h2)) ?_ ?_ ?_ ?_ <;>
      simp only [fw, outside_cons, outside_nil, and_true] <;> omega
  have gR : Mj.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine rd_chain hM hJ (Or.inr hgrt) ?_ ?_ ?_ ?_ <;>
      simp only [fw, outside_cons, outside_nil, and_true] <;> omega
  refine ⟨hal, hsp1, hsp2, by rw [acc_chain hM hJ]; exact hacc, hg1, by rw [acc_chain hM hJ]; exact hg2,
    by rw [gR]; exact hg3, by unfold Apart; omega, by rw [slot _ (by omega)]; exact r912,
    by rw [slot _ (by omega)]; exact r840, by rw [slot _ (by omega)]; exact r848, by rw [slot _ (by omega)]; exact r856,
    hst1, by rw [acc_chain hM hJ]; exact hst2, by rw [stR _ _ (by omega) (by omega)]; exact hn0,
    by unfold Apart; omega, hstg, by rw [slot _ (by omega)]; exact rfp,
    by rw [slot _ (by omega)]; exact rlr⟩

/-- what the return state satisfies, from the loop exit (memory `M`) -/
@[reducible] def TailPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp k0 st n0 zp zc zzp zzc : Nat)
    (r18 r29 : BitVec 64) (M0 M : Memory) (s' : State) : Prop :=
  ∃ (M' Mj : Memory) (p l c : Nat), Mem R b L g sp M0 M' zp zc zzp zzc ∧
    M'.readLE zzp (8 * n) = Exp.montgomery n (M.readLE zp (8 * n)) 1 (M0.readLE mp (8 * n)) k0 ∧
    JoinPost R b L g sp n zzp zzc
      (if M0.readLE mp (8 * n) ≤ M'.readLE zzp (8 * n) then 0 else M'.readLE zzp (8 * n)) M' p l c Mj ∧
    FinPost sp g st n0 p (Expmc.normL Mj p l) c r18 r29 Mj s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 from the main loop's exit to the return -/
theorem exitRet (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat)
    {ext : List (Nat × Nat)} (M0 : Memory) (r18 r29 f29 : BitVec 64) (onep st n0 : Nat)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0) (hce0 : CallW.CEnv R L g sp 4304 1040 M0)
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm0 : NatNorm M0 mp n)
    (hone : OneIn R L sp n M0 onep) (hone1 : M0.readLE onep (8 * n) = 1) (r816 : M0.readLE (sp + 816) 8 = onep)
    (hk : (k0 * M0.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M0.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M0) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 1040))
    (hext1 : (onep, 8 * n) ∈ ext) (hext2 : (st, 24) ∈ ext)
    (S : State) (zp zc zzp zzc : Nat) (M : Memory) (hpc : S.pc = BitVec.ofNat 64 exit)
    (hsp : S.sp = BitVec.ofNat 64 sp) (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zzp)
    (h13 : S.regs 13 = BitVec.ofNat 64 n) (h14 : S.regs 14 = BitVec.ofNat 64 zc) (h15 : S.regs 15 = BitVec.ofNat 64 zzc)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 mc) (h12 : S.regs 12 = BitVec.ofNat 64 k0)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M)
    (hB : Bufs R L g sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 M zp zc zzp zzc) :
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (TailPost R b L g sp n mp k0 st n0 zp zc zzp zzc r18 r29 M0 M)) := by
  have hB' := hB
  obtain ⟨hBz, hBzz, -, -, -, -, -, -, -, -, -, -, hext⟩ := hB'
  have ho := hext _ hext1
  have hs := hext _ hext2
  have hst' := hst
  obtain ⟨he, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hst'
  obtain ⟨-, hsp1, -, -, -, -, -, hwrt, -, hgrt, -⟩ := he
  have hgw4 : Apart (g + 16) 8 (sp - 4304) (4304 + 1040) := hce0.2.2.2.2.2.2.2.2.1
  refine exA impl hap R hclr hmv ret hret _ b L g sp n mp mc k0 yp ylen Y tbl pp pcap M0 r18 f29 onep hst hone hone1
    r816 S zp zc zzp zzc M hpc hsp h0 h1 h13 h14 h15 h2 h3 h9 h11 h12 h18 h28 h29 hmem hB hM ho.1 ho.2 ?_
  intro S' M' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 hM' q400 q160 q168 hval
  have hZ : M.readLE zp (8 * n) < Exp.B ^ n := FvModexp.Expmc.readLE_lt_B M zp n
  refine exB impl hap R hmk hmv hserv ret hret _ b L g sp n mp mc k0 yp ylen Y tbl pp pcap M0 r18 f29 hst hce0 hmw4
    hnm0 S' zp zc zzp zzc M' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 hB hM' q400 q160 q168
    (by rw [hval]; exact Exp.mont_one_le n _ _ k0 hn hZ hmB hk) ?_
  intro Sj p l c Mj b1 b2 b3 b4 b5 b6 b7 b8 b9 hJ
  have hJ' := hJ
  obtain ⟨_, _, _, _, _, _, _, _, _, hlc, hc64, _, _, hpa⟩ := hJ'
  have hfj := finEnv_chain hM' hJ hfe hwrt hgrt hsth hs.1 hs.2 hBz.2.2.2.2.2.2 hBzz.2.2.2.2.2.2 hBz.2.2.2.2.2.1
    hBzz.2.2.2.2.2.1 hgw4 hstw4
  rw [← njoin_eq] at b1
  refine (fin impl hap ret hret sp g st n0 p c r18 r29 Mj (by have := hc64.2; omega) hfj l Sj b1 b2 b3 b4 b5 b6 b7 b9 hlc hpa).mono ?_
  intro o ho'
  cases o with
  | returned s' => exact ⟨M', Mj, p, l, c, hM', hval, hJ, ho'⟩
  | stub _ _ _ => exact ho'.elim

end FvModexp.Arm64.W4Loop
