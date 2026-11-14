import FvModexp.Proofs.Amd64.Exp.W4Posts2
import FvModexp.Proofs.Amd64.Exp.W4Pre4
import FvModexp.Proofs.Amd64.Exp.W4Zm
import FvModexp.Proofs.Amd64.Exp.W4Zm2

set_option autoImplicit false

/-!
# window-4 (amd64): from the end of the power table (`j4` = fn+0xac5) to the return (agent expmc s49)

Twin of `Arm64.W4Mid2.j4Ret`. `zm1` (`z = z.make(2n)`) → `zm2` (`zz = zz.make(2n)`) → `zjRet4`. The `Pre4` facts are
moved along both `ZPost` frames (`Pre4.frame`); the buffer facts at `zj` come from `bufs_mk`: each buffer is the old
array (the caller's `OldA` facts, valid when it is reused, i.e. `2n ≤ cap`) or a fresh one (`InRanges R.rt ∧
ApartAll` the live set at its allocation, hence apart from every held object).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv TailPost step FL)

/-- a buffer after `make` is apart from a held object: old array (caller's fact) or fresh -/
theorem ap_or {R : RtInv} {L : List (Nat × Nat)} {n p c p' c' a k : Nat}
    (hor : (p' = p ∧ c' = c) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hc : 2 * n ≤ c') (hold : 2 * n ≤ c → Apart p (8 * c) a k) (hh : InRanges a k L ∨ Outside a k R.rt) :
    Apart p' (8 * c') a k := by
  rcases hor with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
  · exact hold hc
  · exact apart_held hin hap hh

theorem HeldO.ext {R : RtInv} {L L' : List (Nat × Nat)} {n mp yp ylen onep st : Nat} {pp : Nat → Nat}
    (h : HeldO R L n mp yp ylen onep st pp) (hx : LiveExt R L L') : HeldO R L' n mp yp ylen onep st pp :=
  ⟨hx.held h.1, hx.held h.2.1, fun d hd => hx.held (h.2.2.1 d hd), hx.held h.2.2.2.1, hx.held h.2.2.2.2⟩

theorem oldA_of {R : RtInv} {L : List (Nat × Nat)} {n mp yp ylen onep st p c p' c' : Nat} {pp : Nat → Nat}
    (hor : (p' = p ∧ c' = c) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) (hc : 2 * n ≤ c')
    (hold : 2 * n ≤ c → OldA n mp yp ylen onep st pp p c) (hh : HeldO R L n mp yp ylen onep st pp) :
    OldA n mp yp ylen onep st pp p' c' :=
  ⟨ap_or hor hc (fun h => (hold h).1) hh.1, ap_or hor hc (fun h => (hold h).2.1) hh.2.1,
    fun d hd => ap_or hor hc (fun h => (hold h).2.2.1 d hd) (hh.2.2.1 d hd),
    ap_or hor hc (fun h => (hold h).2.2.2.1) hh.2.2.2.1, ap_or hor hc (fun h => (hold h).2.2.2.2) hh.2.2.2.2⟩

theorem bufs_mk {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp yp ylen onep st zp zc zzp zzc : Nat}
    {pp : Nat → Nat} {M : Memory}
    (hz : Buf R L g fs sp n M zp zc) (hzz : Buf R L g fs sp n M zzp zzc) (ha : Apart zp (8 * zc) zzp (8 * zzc))
    (oz : OldA n mp yp ylen onep st pp zp zc) (ozz : OldA n mp yp ylen onep st pp zzp zzc) :
    Bufs R L g fs sp n mp yp ylen pp [(onep, 8 * n), (st, 24)] M zp zc zzp zzc := by
  refine ⟨hz, hzz, ha, oz.1, ozz.1, oz.2.1, ozz.2.1, fun d hd => ⟨oz.2.2.1 d hd, ozz.2.2.1 d hd⟩, ?_⟩
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨oz.2.2.2.1, ozz.2.2.2.1⟩
  · exact ⟨oz.2.2.2.2, ozz.2.2.2.2⟩

theorem acc_of_in {R : RtInv} {L : List (Nat × Nat)} {g fs sp : Nat} {M : Memory} {ws : List (Nat × Nat)}
    (he : Env R L g fs sp M) (hin : ∀ q ∈ ws, sp - 4296 ≤ q.1 ∧ q.2 ≤ sp - 4296 + (4296 + 0x3c0)) :
    ∀ q ∈ ws, q.1 < q.2 → M.accessible q.1 (q.2 - q.1) true = true := fun q hq _ =>
  Arm64.Memory.accessible_sub (m := M) he.2.2.2.1 (Or.inr rfl) (hin q hq).1 (by have := (hin q hq).2; omega)

theorem low1 (sp : Nat) : LowW sp (zw1 sp) := by
  intro q hq; simp only [zw1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> simp only <;> omega

theorem low2 (sp : Nat) : LowW sp (zw2 sp) := by
  intro q hq; simp only [zw2, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp only <;> omega

/-- a slot above `zw1` keeps its word along the `z.make` frame -/
theorem slot1 {R : RtInv} {sp K : Nat} {M M' : Memory} (hF : MemFrame M M' (R.rt ++ zw1 sp))
    (hrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt) (h0 : 4296 ≤ sp) (hK : 0x90 ≤ K) (hK' : K + 8 ≤ 0x3c0) :
    M'.readLE (sp + K) 8 = M.readLE (sp + K) 8 :=
  hF.readLE _ _ (by
    simp only [zw1, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hrt.of_sub (by omega) (by omega), by omega, by omega⟩)

/-- the held objects of `zjRet` from `Pre4` -/
theorem heldO_of {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y yi Mv : Nat}
    {pp tbl : Nat → Nat} {onep st n0 bp r : Nat} {M : Memory}
    (h : Pre4 R L sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M) (he : Env R L g fs sp M) :
    HeldO R L n mp yp ylen onep st pp := by
  refine ⟨h.2.1.2.2.1, h.2.2.1.2.2.1, fun d hd => (h.2.2.2.2.2.2.1 d hd).2.2.1, ?_, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with h1 | ⟨rfl, h4⟩
  · exact h1.2.2.1
  · have hwrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt := he.2.2.2.2.2.2.2.1
    have := he.2.1
    exact Or.inr (hwrt.of_sub (by omega) (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- window-4 (amd64) from the end of the power table (`j4` = fn+0xac5) to the return -/
theorem j4Ret {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y yi Mv zp zc zzp zzc : Nat} {pp tbl : Nat → Nat}
    {M : Memory} {r5 : W64} {onep st n0 bp r : Nat}
    (he : Env R L g fs sp M) (hP : Pre4 R L sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hk0 : k0 < 2 ^ 64)
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g fs sp n M zp zc ∧ zp % 8 = 0)
    (hzzc : zzc < 2 ^ 40) (hzz : 2 * n ≤ zzc → Buf R L g fs sp n M zzp zzc ∧ zzp % 8 = 0)
    (hoz : 2 * n ≤ zc → OldA n mp yp ylen onep st pp zp zc)
    (hozz : 2 * n ≤ zzc → OldA n mp yp ylen onep st pp zzp zzc)
    (hzzz : 2 * n ≤ zc → 2 * n ≤ zzc → Apart zp (8 * zc) zzp (8 * zzc))
    (r3d0 : M.readLE (sp + 0x3d0) 8 = zc) (r3c0 : M.readLE (sp + 0x3c0) 8 = zp) (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (ra0 : M.readLE (sp + 0xa0) 8 = zzc) (r188 : M.readLE (sp + 0x188) 8 = zzp)
    (hacc2 : M.accessible (sp + 0x3c0) 0x20 false = true)
    (hokm : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4])
    (hb1 : zc < 2 * n → blockSize (8 * (2 * n + 4)) true ≤ b)
    (hb2 : zzc < 2 * n → 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])
    (hinv : R.inv b L g (view R.rt L M))
    (hkk : (k0 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hbp : bp < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6208293) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (M1 M2 : Memory) (zp1 zc1 zzp2 zzc2 : Nat) (L1 L2 : List (Nat × Nat)) (b1 b2 : Nat),
        ZPost R L L1 b b1 g fs sp n M M1 (zw1 sp) zp zc zp1 zc1 ∧
        ZPost R L1 L2 b1 b2 g fs sp n M1 M2 (zw2 sp) zzp zzc zzp2 zzc2 ∧
        ZjPost R b2 L2 g fs sp n mp yp ylen zp1 zc1 zzp2 zzc2 k0 pp (zjVal n Mv k0 tbl Y ylen yi) st n0 onep bp M2 s') := by
  have hc := codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmkL := MakesliceLiveContract64.of_codeIn hc hmk
  have hs0 : 4296 ≤ sp := he.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt := he.2.2.2.2.2.2.2.1
  have hd : Extracted.program.DataLoaded M := hP.1
  have r3b0 : M.readLE (sp + 0x3b0) 8 = n := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hH := heldO_of hP he
  refine zm1 impl hmkL b L g fs sp n zp zc M r5 he hn hn16 hzc hz hd r3d0 r3c0 r3b0 r78
    (fun h => ⟨hokm, hb1 h⟩) hinv hacc2 S hpc hsp hmem h5 h14 hfs hx15 hdf ?_
  intro S1 zp1 zc1 L1 b1 hpc1 hsp1 h51 h141 hfs1 hx151 hdf1 h01 h21 h31 hZ1
  have hZ1' := hZ1
  obtain ⟨he1, hz1, hz18, hx1, hb1', hF1, hL1, hinv1, hrg1, hor1⟩ := hZ1'
  have hP1 := Pre4.frame hP he hF1 hL1 hx1 hrg1 hro (acc_of_in he (zw1_in sp)) (low1 sp) hn hyl
  have hzz1 : 2 * n ≤ zzc → Buf R L1 g fs sp n S1.mem zzp zzc ∧ zzp % 8 = 0 := fun h =>
    ⟨buf_ext hx1 (hzz h).1 hF1, (hzz h).2⟩
  have hb1'' : zzc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b1 := by
    intro h
    refine ⟨hokm, ?_⟩
    have := hb2 h
    rcases hor1 with ⟨-, -, -, rfl⟩ | -
    · omega
    · omega
  refine zm2 impl hmkL b1 L1 g fs sp n zp1 zc1 zzp zzc S1.mem r5 he1 hn hn16 (by have := hz1.1; omega) hz1.2.1
    (by have := hz1.2.2.2.1; omega) hzzc hzz1 hP1.1 (by rw [slot1 hF1 hwrt hs0 (by omega) (by omega)]; exact r3b0)
    (by rw [slot1 hF1 hwrt hs0 (by omega) (by omega)]; exact ra0)
    (by rw [slot1 hF1 hwrt hs0 (by omega) (by omega)]; exact r188) hb1'' hinv1 S1 hpc1 hsp1 rfl h51 h141 hfs1 hx151
    hdf1 h01 h21 h31 ?_
  intro S2 zzp2 zzc2 L2 b2 hpc2 hsp2 h52 h142 hfs2 hx152 hdf2 h02 h22 h12 h122 h112 hZ2 r88 r168
  have hZ2' := hZ2
  obtain ⟨he2, hzz2, hzz28, hx2, -, hF2, hL2, hinv2, hrg2, hor2⟩ := hZ2'
  have hP2 := Pre4.frame hP1 he1 hF2 hL2 hx2 hrg2 hro (acc_of_in he1 (zw2_in sp)) (low2 sp) hn hyl
  have hz2 : Buf R L2 g fs sp n S2.mem zp1 zc1 := buf_ext hx2 hz1 hF2
  -- old-array / fresh facts of both buffers
  have oz1 := oldA_of (hor1.imp (fun h => ⟨h.1, h.2.1⟩) id) hz1.1 hoz hH
  have ozz2 := oldA_of (hor2.imp (fun h => ⟨h.1, h.2.1⟩) id) hzz2.1 hozz (hH.ext hx1)
  have ha : Apart zp1 (8 * zc1) zzp2 (8 * zzc2) := by
    rcases hor2 with ⟨rfl, rfl, -⟩ | ⟨hin2, hap2⟩
    · rcases hor1 with ⟨rfl, rfl, -⟩ | ⟨hin1, hap1⟩
      · exact hzzz hz1.1 hzz2.1
      · exact apart_held hin1 hap1 (hzz hzz2.1).1.2.2.2.2.1
    · exact (apart_held hin2 hap2 hz1.2.2.2.2.1).symm
  have hB := bufs_mk hz2 hzz2 ha oz1 ozz2
  refine ReachesRet.mono (zjRet4 hap hclr hmv hmk hmvok hwt hro he2 hP2 hn hn16 hmc hmc' hk0 hyl hyl' hyi0 hz2 hzz2
    hz18 hzz28 hB r168 r88 hokS hinv2 hkk hmB hbp S2 hpc2 hsp2 rfl h52 h142 hfs2 hx152 hdf2 h02 h22 h12 h112 h122) ?_
  exact fun s h => ⟨S1.mem, S2.mem, zp1, zc1, zzp2, zzc2, L1, L2, b1, b2, hZ1, hZ2, h⟩

end FvModexp.Amd64.W4Pro
