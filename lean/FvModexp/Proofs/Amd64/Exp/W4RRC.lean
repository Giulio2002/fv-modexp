import FvModexp.Proofs.Amd64.Exp.W4Cut
import FvModexp.Proofs.Amd64.Exp.W4RRRet

set_option autoImplicit false

/-!
# window-4 prologue (amd64): `rrRetC` — `rrRet` (divRet → return) from the `RR`-section context
(agent expmc s52; twin of `Arm64.W4RRC`)

`ZZ` = the facts about the `zz` buffer (`zz = 2^(128n)` lives there at the division). `rrRetC` derives `rrRet`'s
premises from `Ctx` (window `K ≥ 41512` shrunk to the loop's fixed frame) + `ZZ` + the per-step facts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem rrRetC (hJ4 : FvModexp.Amd64.W4Pro.J4Spec) (hP01 : FvModexp.Amd64.W4Pro.P01Spec) {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r t rp rl rc zzp zzc : Nat} {ex : List (Nat × Nat)}
    {M : Memory} {r5 : W64}
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    (hZ : ZZ R L g fs sp n mp xp yp ylen zp zc st zzp zzc M)
    (ht : t < 2 ^ 64) (hfbp : fbp < 2 ^ 64) (sd8 : M.readLE (sp + 0xd8) 8 = t) (s78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (s1a0 : M.readLE (sp + 0xa0) 8 = zzc) (s188 : M.readLE (sp + 0x188) 8 = zzp)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n)
    (hslen : stLen M st + 17 * n + 3 ≤ 2 ^ 16)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (17 * n) + 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4296) (4296 + 0x3c0))
    (hrS : Apart rp (8 * rl) st 24) (hrF : Apart rp (8 * rl) (stFree M st).1 (stFree M st).2)
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 divRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h7 : S.regs 7 = BitVec.ofNat 64 rp) (h6 : S.regs 6 = BitVec.ofNat 64 rl) (h8 : S.regs 8 = BitVec.ofNat 64 rc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
        RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (17 * n) st n0 onep fbp
          Mv Xv (M.readLE rp (8 * rl)) M2 s') := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huf, huw, hsu, hstg, hstf, hgl, hgO, hstwb, hwba,
    hcacc, hcrt, hcO, r3a8, r3b0, r3b8, r3d0, r3c0, r398, r390, r3d8, r370, r138, -⟩ := hC
  obtain ⟨hzz, hzz8, hzzm, hzzy, hzzx, hzzc, hzzs, hzzU, hzzz⟩ := hZ
  have hlc := hsok.2.2.2.2.2.1
  have hd : Extracted.program.DataLoaded M := hce.2.2.2.2.2.2.2.2.2.2.2.1
  -- the free part lies in the stack above `l0`
  have fr : ∀ a k, Apart a k (stUp M st l0).1 (stUp M st l0).2 → Apart a k (stFree M st).1 (stFree M st).2 :=
    fun a k h => free_of_up h hl0 hlc
  have frl : ∀ a k, Apart (stUp M st l0).1 (stUp M st l0).2 a k → Apart (stFree M st).1 (stFree M st).2 a k :=
    fun a k h => (free_of_up h.symm hl0 hlc).symm
  have hoz : 2 * n ≤ zc → Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zp (8 * zc) st 24 ∧
      Apart zp (8 * zc) (stFree M st).1 (stFree M st).2 := by
    intro h
    obtain ⟨-, -, o, a1, a2⟩ := hz h
    exact ⟨a1, a2, o.2.2.1, fr _ _ o.2.2.2.1⟩
  have hacc3 : M.accessible (sp + 0x3d8) 8 false = true :=
    M.accessible_sub hcacc (Or.inl rfl) (by omega) (by omega)
  rw [← hxv]
  exact rrRet hJ4 hP01 hap hclr hmv hmk (fun d src k hk => hserv.2.1 d src k hk) hwt hro hSN hserv (Y := Y) (Mv := Mv) (yi := yi)
    (he := he) (hd := hd) (hn := hn) (hn16 := by omega) (hmc := hmc) (hmc' := hmc') (ht := ht) (hm := hm) (hx := hx)
    (hok := fun p => ⟨hserv.2.2.1 _ _ (by omega), hserv.2.1 _ _ _ (by omega)⟩) (hy := hy) (hY := hY) (hyi := hyi)
    (hyl := hyl) (hyl' := hyl') (hyi0 := hyi0) (s398 := r398) (s390 := r390) (s3a8 := r3a8) (s3b0 := r3b0)
    (s3b8 := r3b8) (hnm := hnm) (hMv := hmV) (s78 := s78) (sd8 := sd8) (s370 := r370) (s138 := r138) (hfe := hfe)
    (hsth := hsth) (hzc := hzc) (hz := fun h => ⟨(hz h).1, (hz h).2.1⟩) (hzz := hzz) (hzz8 := hzz8) (hoz := hoz)
    (hzzm := hzzm) (hzzy := hzzy) (hzzs := hzzs) (hzzF := fr _ _ (up_of_arr hzzU (Nat.le_trans hl0 hlc)))
    (hzx := hzzx) (hzca := hzzc) (hzzz := hzzz) (r3d0 := r3d0) (r3c0 := r3c0) (hacc2 := hcacc) (hca := hcrt)
    (hcF := fr _ _ hcO.2.2.2.1) (hcS := hcO.2.2.1) (hokm := hserv.1 _ _ _ (by omega)) (hkk := hkk) (hmB := hmB)
    (hfbp := hfbp) (hsok := hsok) (hn0 := by omega) (hcap := hcap) (hstw := aw_w4 hK hstw) (hstg := hstg)
    (hstf8 := hstf) (hfg := frl _ _ hug) (hff := frl _ _ huf)
    (harr := fun h => ⟨aw_w4 hK (harr h).1, (harr h).2.1, (harr h).2.2⟩) (hfw := frl _ _ (aw_w4 hK huw))
    (hslen := hslen) (hwba := hwba) (hstwb := hstwb) (hstf := fr _ _ hsu) (hmS := hmO.2.2.1)
    (hmF := fr _ _ hmO.2.2.2.1) (hxS := hxO.2.2.1) (hxF := fr _ _ hxO.2.2.2.1) (hyS := hyO.2.2.1)
    (hyF := fr _ _ hyO.2.2.2.1) (hbud := hbud) (hinv := hinv) (s3d8 := r3d8) (hacc3 := hacc3)
    (hokone := fun _ => hserv.1 _ _ _ (by omega)) (s1a0 := s1a0) (s188 := s188) (hrl0 := hrl0) (hrln := hrln)
    (hrc := hrc) (hra := hra) (hr48 := hr48) (hrh := hrh) (hrw := hrw) (hrS := hrS) (hrF := hrF) (hzr := hzr)
    (hzz0 := hzz0) S hpc hsp hmem h7 h6 h8 h5 h14 hfs hx15 hdf

/-- `rrRetC` as the cut statement `RRSpec` (divmc s79; discharged at the top, `W2FunE`) -/
theorem rrSpec (hJ4 : FvModexp.Amd64.W4Pro.J4Spec) (hP01 : FvModexp.Amd64.W4Pro.P01Spec) : RRSpec := @rrRetC hJ4 hP01

end FvModexp.Amd64.W4Pro
