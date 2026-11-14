import FvModexp.Proofs.Amd64.Exp.W2Posts2
import FvModexp.Proofs.Amd64.Exp.W2Mid

set_option autoImplicit false

/-!
# window-2 prologue (amd64): the facts `zjRet` needs, bundled, and their transport along `z.make`/`zz.make`
(agent expmc s48)

`Pre4` = everything `W2Mid.zjRet` takes about the memory and the live set except the two buffers. `Pre4.frame`
moves it along a frame that writes only `R.rt` and low frame words (`[sp-4296, sp+0xd8)`, `[sp+0x170, sp+0x178)`)
with the live set extended by fresh `R.rt` ranges (the `ZPost`s of `W2Zm`/`W2Zm2`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf Bufs Mem Static OneIn FinEnv)

theorem out_low {a k sp : Nat} (h : Apart a k (sp - 4296) (4296 + 0x2a8)) (hs : 4296 ≤ sp) :
    ∀ ws, LowW sp ws → Outside a k ws
  | [], _ => trivial
  | q :: ws, hq => by
    have h1 := hq q (by simp)
    refine ⟨by unfold Apart at h; omega, out_low h hs ws (fun q' hq' => hq q' (by simp [hq']))⟩

theorem out_slot {a k sp : Nat} (h1 : sp + 0xd8 ≤ a) (h2 : a + k ≤ sp + 0x170 ∨ sp + 0x178 ≤ a) :
    ∀ ws, LowW sp ws → Outside a k ws
  | [], _ => trivial
  | q :: ws, hq => by
    have h3 := hq q (by simp)
    refine ⟨by omega, out_slot h1 h2 ws (fun q' hq' => hq q' (by simp [hq']))⟩

set_option maxRecDepth 20000 in
theorem Pre4.frame {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y yi Mv : Nat}
    {pp tbl : Nat → Nat} {onep st n0 bp r : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Pre4 R L sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M) (he : Env R L g fs sp M)
    (hF : MemFrame M M' (R.rt ++ ws)) (hL : LiveFrame M M' L []) (hx : LiveExt R L L')
    (hrg : M'.regions = M.regions) (hro : RoOut R)
    (hwa : ∀ q ∈ ws, q.1 < q.2 → M.accessible q.1 (q.2 - q.1) true = true) (hlw : LowW sp ws)
    (hn : 0 < n) (hyl : 0 < ylen) :
    Pre4 R L' sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M' := by
  obtain ⟨hd, hm, hy, hY, hyi, hent, hbuf, s1, s2, s3, s4, s5, s6, hnm, hmv, hone, hone1, r328, hfe, hsth⟩ := h
  have hs1 : 4296 ≤ sp := he.2.1
  have hs2 : sp + 0x2a8 ≤ 2 ^ 48 := he.2.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt := he.2.2.2.2.2.2.2.1
  have hF0 : MemFrame M M' (R.rt ++ ws ++ []) := by rw [List.append_nil]; exact hF
  have rdh : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Outside a k ws → M'.readLE a k = M.readLE a k :=
    fun a k hh ho => FvModexp.Expmc.held_readLE hh hF0 hL ho trivial
  have rdi : ∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x2a8) →
      M'.readLE a k = M.readLE a k := fun a k hh ha => rdh a k hh (out_low ha hs1 ws hlw)
  have rds : ∀ K, 0xd8 ≤ K → K + 8 ≤ 0x2a8 → (K + 8 ≤ 0x170 ∨ 0x178 ≤ K) →
      M'.readLE (sp + K) 8 = M.readLE (sp + K) 8 := fun K k1 k2 k3 =>
    rdh _ _ (Or.inr (hwrt.of_sub (by omega) (by omega))) (out_slot (by omega) (by omega) ws hlw)
  have inp : ∀ k p, Inp R L sp k M p → Inp R L' sp k M' p := fun k p hp =>
    ⟨by rw [hF.accessible]; exact hp.1, hp.2.1, hx.held hp.2.2.1, hp.2.2.2⟩
  refine ⟨FvModexp.dataLoaded_frame64 hd hrg hro hF hwa, inp _ _ hm, inp _ _ hy,
    by rw [rdi _ _ hy.2.2.1 hy.2.2.2]; exact hY, ?_, fun d hd => ?_, fun d hd => inp _ _ (hbuf d hd),
    by rw [rds 0x280 (by omega) (by omega) (by omega)]; exact s1, by rw [rds 0x278 (by omega) (by omega) (by omega)]; exact s2,
    by rw [rds 0x290 (by omega) (by omega) (by omega)]; exact s3, by rw [rds 0xd8 (by omega) (by omega) (by omega)]; exact s4,
    by rw [rds 0x298 (by omega) (by omega) (by omega)]; exact s5, by rw [rds 0x2a0 (by omega) (by omega) (by omega)]; exact s6,
    ?_, by rw [rdi _ _ hm.2.2.1 hm.2.2.2]; exact hmv, ?_, ?_, by rw [rds 0x210 (by omega) (by omega) (by omega)]; exact r328,
    ?_, hsth.imp (fun h => hx.inRanges_old h) id⟩
  · have hyw := hy.2.2.2
    unfold Apart at hyw
    rw [rdh _ _ (hy.2.2.1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (out_low (by unfold Apart; omega) hs1 ws hlw)]; exact hyi
  · obtain ⟨e1, e2, e3, e4⟩ := hent d hd
    have hbd := hbuf d hd
    refine ⟨by rw [rdi _ _ hbd.2.2.1 hbd.2.2.2]; exact e1, ?_, ?_, ?_⟩
    · rw [show sp + 0x1b0 + 24 * d = sp + (0x1b0 + 24 * d) by omega, rds _ (by omega) (by omega) (by omega),
        ← Nat.add_assoc]; exact e2
    · rw [show sp + 0x1b8 + 24 * d = sp + (0x1b8 + 24 * d) by omega, rds _ (by omega) (by omega) (by omega),
        ← Nat.add_assoc]; exact e3
    · rw [show sp + 0x1c0 + 24 * d = sp + (0x1c0 + 24 * d) by omega, rds _ (by omega) (by omega) (by omega),
        ← Nat.add_assoc]; exact e4
  · rcases hnm with h | h
    · exact Or.inl h
    · right
      have hm4 := hm.2.2.2
      unfold Apart at hm4
      rw [rdh _ _ (hm.2.2.1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
        (out_low (by unfold Apart; omega) hs1 ws hlw)]; exact h
  · rcases hone with h | h
    · exact Or.inl (inp _ _ h)
    · exact Or.inr h
  · rcases hone with h | ⟨rfl, h4⟩
    · rw [rdi _ _ h.2.2.1 h.2.2.2]; exact hone1
    · rw [rdh _ _ (Or.inr (hwrt.of_sub (by omega) (by omega)))]
      · exact hone1
      · exact out_slot (by omega) (Or.inl (by omega)) ws hlw
  · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hfe
    have hstw := f12
    unfold Apart at hstw
    refine ⟨f1, f2, f3, by rw [hF.accessible]; exact f4, by rw [rds 0x260 (by omega) (by omega) (by omega)]; exact f5,
      by rw [rds 0x228 (by omega) (by omega) (by omega)]; exact f6, by rw [rds 0x230 (by omega) (by omega) (by omega)]; exact f7,
      by rw [rds 0x238 (by omega) (by omega) (by omega)]; exact f8, f9, by rw [hF.accessible]; exact f10, ?_, f12,
      by rw [rds 0x268 (by omega) (by omega) (by omega)]; exact f13, by rw [rds 0x270 (by omega) (by omega) (by omega)]; exact f14,
      f15⟩
    rw [rdh _ _ (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (out_low (by unfold Apart; omega) hs1 ws hlw)]; exact f11

set_option maxRecDepth 20000 in
/-- `zjRet` with its memory facts bundled (`Pre4`) -/
theorem zjRet4 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
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
    (hz : Buf R L g fs sp n M zp zc) (hzz : Buf R L g fs sp n M zzp zzc) (hz8 : zp % 8 = 0) (hzz8 : zzp % 8 = 0)
    (hB : Bufs R L g fs sp n mp yp ylen pp [(onep, 8 * n), (st, 24)] M zp zc zzp zzc)
    (r168 : M.readLE (sp + 0x170) 8 = zp) (r88 : M.readLE (sp + 0x88) 8 = zc)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])
    (hinv : R.inv b L g (view R.rt L M))
    (hkk : (k0 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hbp : bp < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 zj) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h1 : S.regs 1 = BitVec.ofNat 64 zzp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (ZjPost R b L g fs sp n mp yp ylen zp zc zzp zzc k0 pp (zjVal n Mv k0 tbl Y ylen yi) st n0 onep bp M) := by
  obtain ⟨hd, hm, hy, hY, hyi, hent, hbuf, s1, s2, s3, s4, s5, s6, hnm, hmv', hone, hone1, r328, hfe, hsth⟩ := hP
  subst hmv'
  exact zjRet hap hclr hmv hmk hmvok hwt hro b L g fs sp n mp mc k0 yp ylen Y yi zp zc zzp zzc pp tbl M r5 onep st n0 bp r
    he hd hn hn16 hmc hmc' hk0 hyl hyl' hm hy hY hyi hyi0 hz hzz hz8 hzz8 hent hbuf hB s1 s2 r168 r88 s3 s4 s5 s6 hokS
    hinv hnm hone hone1 r328 hkk hmB hfe hsth hbp S hpc hsp hmem h5 h14 hfs hx15 hdf h0 h2 h1 h11 h12

end FvModexp.Amd64.W2Pro
