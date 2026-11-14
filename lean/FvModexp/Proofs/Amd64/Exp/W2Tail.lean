import FvModexp.Proofs.Amd64.Exp.W2Posts
import FvModexp.Proofs.Amd64.Exp.W2ExC
import FvModexp.Proofs.Amd64.Exp.W2Fin
import FvModexp.Proofs.Common.ExpFinal
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# window-2 (amd64), from the main loop's exit to the return (nat.go:1477-1490; agent expmc s47)

Twin of `Arm64.W2Loop.exitRet`. `exA` (`zz = zz.montgomery(z, one, …)`) → `exC` (final reduction, join) → `fin`
(`zz.norm()`, deferred `stk.restore`, return). The conclusion lists the facts of the three stages: `Mem` (anchor `M0`
→ memory `M'` at the first cmp), `JoinPost` (`M'` → join memory `Mj`, value `if m ≤ zz then 0 else zz` with
`zz = montgomery(z, 1)`), `FinPost` (`Mj` → return).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W2Loop

/-- a held range outside the written stack ranges and the two buffers reads at the join as at the anchor -/
theorem rd_chain {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zp zc zzp zzc V p l c a k : Nat}
    {M0 M' Mj : Memory} (hM : Mem R b L g sp M0 M' zp zc zzp zzc)
    (hJ : JoinPost R b L g sp n zzp zzc V M' p l c Mj) (hh : InRanges a k L ∨ Outside a k R.rt)
    (h1 : Outside a k (fw sp))
    (h2 : Outside a k [(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x190, sp + 0x198)])
    (hz : Outside a k [(zp, zp + 8 * zc)]) (hzz : Outside a k [(zzp, zzp + 8 * zzc)]) :
    Mj.readLE a k = M0.readLE a k := by
  obtain ⟨hF, hLF⟩ := hM.1
  obtain ⟨_, _, _, _, _, _, hF2, hLF2, _⟩ := hJ
  rw [FvModexp.Expmc.held_readLE hh hF2 hLF2 h2 hzz]
  refine FvModexp.Expmc.held_readLE hh hF hLF h1 ?_
  simp only [outside_cons, outside_nil, and_true] at hz hzz ⊢
  exact ⟨hz, hzz⟩

theorem acc_chain {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zp zc zzp zzc V p l c : Nat}
    {M0 M' Mj : Memory} (hM : Mem R b L g sp M0 M' zp zc zzp zzc)
    (hJ : JoinPost R b L g sp n zzp zzc V M' p l c Mj) (a k : Nat) (w : Bool) :
    Mj.accessible a k w = M0.accessible a k w := by
  obtain ⟨_, _, _, _, _, _, hF2, _, _⟩ := hJ
  rw [hF2.accessible, hM.1.1.accessible]

/-- the join's `FinEnv` from the anchor's -/
theorem finEnv_chain {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zp zc zzp zzc V p l c st n0 bp r : Nat}
    {M0 M' Mj : Memory} (hM : Mem R b L g sp M0 M' zp zc zzp zzc)
    (hJ : JoinPost R b L g sp n zzp zzc V M' p l c Mj) (he : FinEnv sp st n0 bp r M0)
    (hwrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstz : Apart zp (8 * zc) st 24) (hstzz : Apart zzp (8 * zzc) st 24)
    (hsz : Apart zp (8 * zc) (sp - 4296) (4296 + 0x2a8)) (hszz : Apart zzp (8 * zzc) (sp - 4296) (4296 + 0x2a8)) :
    FinEnv sp st n0 bp r Mj := by
  obtain ⟨hal, hsp1, hsp2, hacc, r378, r340, r348, r350, hst1, hsta, hn0, hstw, r380, r388, hr47⟩ := he
  unfold Apart at hstz hstzz hsz hszz hstw
  have slot : ∀ a, (sp + 0x228 ≤ a ∧ a + 8 ≤ sp + 0x240) ∨ (sp + 0x260 ≤ a ∧ a + 8 ≤ sp + 0x278) →
      Mj.readLE a 8 = M0.readLE a 8 := by
    intro a ha
    refine rd_chain hM hJ (Or.inr (hwrt.of_sub (by omega) (by omega))) ?_ ?_ ?_ ?_ <;>
      simp only [fw, outside_cons, outside_nil, and_true] <;> omega
  have stR : ∀ a k, st ≤ a → a + k ≤ st + 24 → Mj.readLE a k = M0.readLE a k := by
    intro a k h1 h2
    refine rd_chain hM hJ (hsth.imp (fun h => h.sub h1 h2) (fun h => h.of_sub h1 h2)) ?_ ?_ ?_ ?_ <;>
      simp only [fw, outside_cons, outside_nil, and_true] <;> omega
  refine ⟨hal, hsp1, hsp2, by rw [acc_chain hM hJ]; exact hacc, by rw [slot _ (by omega)]; exact r378,
    by rw [slot _ (by omega)]; exact r340, by rw [slot _ (by omega)]; exact r348, by rw [slot _ (by omega)]; exact r350,
    hst1, by rw [acc_chain hM hJ]; exact hsta, by rw [stR _ _ (by omega) (by omega)]; exact hn0,
    by unfold Apart; omega, by rw [slot _ (by omega)]; exact r380, by rw [slot _ (by omega)]; exact r388, hr47⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-2 from the main loop's exit to the return -/
theorem exitRet {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory} (hd : Extracted.program.DataLoaded M0)
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) (hnm : NatNorm M0 mp n)
    {onep st n0 bp r : Nat} (hone : OneIn R L sp n M0 onep) (hone1 : M0.readLE onep (8 * n) = 1)
    (r328 : M0.readLE (sp + 0x210) 8 = onep)
    (hk : (k0 * M0.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M0.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp st n0 bp r M0) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt) (hbp : bp < 2 ^ 64)
    (hext1 : (onep, 8 * n) ∈ ext) (hext2 : (st, 24) ∈ ext)
    (S : State) (r5 : W64) (zp zc zzp zzc : Nat)
    (hpc : S.rip = BitVec.ofNat 64 exit) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (h5 : S.regs 5 = r5)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h8 : S.regs 8 = BitVec.ofNat 64 zzp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc)
    (h3 : S.regs 3 = BitVec.ofNat 64 mp) (h6 : S.regs 6 = BitVec.ofNat 64 k0) (h10 : S.regs 10 = BitVec.ofNat 64 mc)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (r140 : S.mem.readLE (sp + 0x148) 8 = n) (hz8 : zzp % 8 = 0) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (TailPost R b L g fs sp n mp k0 st n0 bp zp zc zzp zzc M0 S.mem) := by
  have hB' := hB
  obtain ⟨hBz, hBzz, -, -, -, -, -, -, hext⟩ := hB'
  have ho := hext _ hext1
  have hs := hext _ hext2
  have he := hst.1
  have hn := hst.2.1
  have hwrt := he.2.2.2.2.2.2.2.1
  refine exA hap hclr hmv hst hone hone1 r328 S r5 zp zc zzp zzc _ hpc hsp h5 h14 hfs hx15 hdf h0 h2 h8 h11 h12 h3 h6
    h10 hB hM r140 rfl ho.1 ho.2 ?_
  intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 hM' q188 q98 qa0 hval
  have hZ : S.mem.readLE zp (8 * n) < Exp.B ^ n := FvModexp.Expmc.readLE_lt_B S.mem zp n
  refine exC hap hmk hmv hmvok hwt hro hd hst hnm S' r5 zp zc zzp zzc a1 a2 a3 a4 a5 (by rw [a6, hfs]) a7 a8 a9 a10
    a12 a13 hB hM' hz8 q188 q98 qa0 (by rw [hval]; exact Exp.mont_one_le n _ _ k0 hn hZ hmB hk) ?_
  intro Sj p l c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 hJ
  have hfj := finEnv_chain hM' hJ hfe hwrt hsth hs.1 hs.2 hBz.2.2.2.2.2.1 hBzz.2.2.2.2.2.1
  have hJ' := hJ
  obtain ⟨_, _, _, _, _, _, _, _, _, hlc, ⟨hc0, hc40⟩, hlive, _, hpa⟩ := hJ'
  have hp : p < 2 ^ 64 := by have := (hlive hc0).2.2.2; omega
  refine (fin hap sp g fs st n0 bp r p c Sj.mem hc40 hp hbp hfj l Sj b1 b2 b4 b5 b6 b7 b8 b9 b10 rfl hlc
    hpa).mono ?_
  intro s' h
  exact ⟨S'.mem, Sj.mem, p, l, c, hM', hval, hJ, h⟩

end FvModexp.Amd64.W2Loop
