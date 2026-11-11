import FvModexp.Proofs.Amd64.Nat.LibFree
import FvModexp.Proofs.Amd64.Conv

/-!
# `nat.expNN.deferwrap1` (amd64): the deferred `stk.free()` of `nat.expNN` — the amd64 twin of Arm64/Nat/Free.lean

```
PUSHQ BP; MOVQ SP, BP; SUBQ $0x18, SP
MOVQ 0x8(DX), CX          ; stk (DX = the closure context)
MOVQ $0x0, 0x8(CX)        ; stk.w = stk.w[:0]
LEAQ stackPool, AX; LEAQ type:*big.stack, BX
CALL sync.(*Pool).Put     ; Put(&stackPool, (type:*big.stack, stk))
ADDQ $0x18, SP; POPQ BP; RET
```
`Put` runs with `RSP' = RSP - 0x28`; the window is `[RSP - 4136, RSP)` (the return slot `[RSP, RSP+8)` is read only).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Pool
  Janus.Contracts.PoolAmd64

namespace FvModexp.Amd64.Free

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN.deferwrap1"

/-- `type:*big.stack` (the interface type word passed to `Put`) -/
abbrev stkT : Nat := Extracted.dataAddr.«type:*big.stack#6bae7c96»
/-- `math/big.stackPool` -/
abbrev poolA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.stackPool»

/-- the captured `stk` -/
@[reducible] def stkOf (s : State) : Nat := s.mem.readLE ((s.regs 2).toNat + 8) 8

/-- The context of a call of the closure. -/
def Pre (R : RtInv) (b : Nat) (L rs : List (Nat × Nat)) (B : Nat) (s : State) : Prop :=
  (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4136 < (s.regs 4).toNat ∧
    (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4136) 4144 true = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    (s.regs 2).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 2).toNat + 8) 8 false = true ∧
    Apart ((s.regs 2).toNat + 8) 8 ((s.regs 4).toNat - 4136) 4144 ∧
    SliceObj B s.mem (stkOf s) rs ∧ Apart (stkOf s) 24 ((s.regs 4).toNat - 4136) 4144 ∧
    Apart (stkOf s + 8) 8 ((s.regs 14).toNat + 16) 8 ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4136) 4144 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    (∀ r ∈ rs, r ∈ L) ∧ R.ok (cA "sync.(*Pool).Put") [poolA] ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    LiveSep L [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 8)] ∧ Outside ((s.regs 4).toNat - 4136) 4144 R.rt

/-- What it guarantees. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L rs : List (Nat × Nat)) (s s' : State) : Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.fsBase = s.fsBase ∧ s'.df = s.df) ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat), (stkOf s + 8, stkOf s + 16)]) ∧
    LiveFrame s.mem s'.mem L [(stkOf s + 8, stkOf s + 16)] ∧
    R.inv b (dropAll L rs) (s.regs 14).toNat (view R.rt (dropAll L rs) s'.mem)

/-- `len = 0` stored into a pooled-shape header keeps the shape. -/
theorem sliceObj_len0 {B : Nat} {m m' : Janus.Arm64.Memory} {d : Nat} {rs ws : List (Nat × Nat)}
    (h : SliceObj B m d rs) (hf : MemFrame m m' ws) (hd0 : Outside d 8 ws) (hd16 : Outside (d + 16) 8 ws)
    (h0 : m'.readLE (d + 8) 8 = 0) : SliceObj B m' d rs := by
  unfold SliceObj at h ⊢
  obtain ⟨h0', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have e0 : m'.readLE d 8 = m.readLE d 8 := hf.readLE _ _ hd0
  have e2 : m'.readLE (d + 16) 8 = m.readLE (d + 16) 8 := hf.readLE _ _ hd16
  simp only [e0, e2, h0, hf.accessible]
  exact ⟨h0', h1, h2, h3, Nat.zero_le _, h5, h6, h7, h8, h9, h10, h11⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem sum (impl : List Amd64.Segment) (R : RtInv) (B : Nat)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R stkT (SliceObj B))
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibFree.program.link impl) (segAddr Extracted.program fn) (Pre R b L rs B) (Post R b L rs) := by
  intro s hpc ⟨hg1, hg2, hg3, hal, ha, hw, hra, hc1, hc2, hca, hsh, hsw, hsg, hgw, hgr, hrs, hok, hinv, hLs, hout⟩
  have hca' := hca; have hsw' := hsw; have hsg' := hsg; have hgw' := hgw
  unfold Apart at hca' hsw' hsg' hgw'
  have hsh' := hsh
  obtain ⟨hs0, hs8, hs48, hsacc, -, -, -, -, -, -, -, -⟩ := hsh'
  simp only [stkOf] at hsh hsw' hsg' hs0 hs8 hs48 hsacc
  have hacc8 : s.mem.accessible (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hsacc (by omega) (by omega)
  have hacc8' : s.mem.accessible ((s.regs 4).toNat - 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  janus64_run [hacc8, hacc8'] until [cA "sync.(*Pool).Put"]
  generalize hM1 : ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 0).writeLE ((s.regs 4).toNat - 40) 8 6191629 = M1
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF1 : MemFrame s.mem M1 [((s.regs 4).toNat - 8, (s.regs 4).toNat),
      (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8, s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16),
      ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] := by
    rw [← hM1]; janus_frame
  have hk1 : ∀ a n, (a + n ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) →
      (a + n ≤ s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8 ∨ s.mem.readLE ((s.regs 2).toNat + 8) 8 + 16 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 32 ≤ a) →
      M1.readLE a n = s.mem.readLE a n := fun a n h1 h2 h3 =>
    hF1.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  have hlen0 : M1.readLE (s.mem.readLE ((s.regs 2).toNat + 8) 8 + 8) 8 = 0 := by
    rw [← hM1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have hret : M1.readLE ((s.regs 4).toNat - 40) 8 = 6191629 := by
    rw [← hM1, Janus.Arm64.Memory.readLE_writeLE_self]
  have hhdr : (s.mem.readLE ((s.regs 2).toNat + 8) 8, s.mem.readLE ((s.regs 2).toNat + 8) 8 + 24) ∈ L := by
    apply hrs; have h' := hsh; unfold SliceObj at h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e⟩ := h'
    rw [e]; exact List.mem_cons_self
  have hinv1 : R.inv b L (s.regs 14).toNat (view R.rt L M1) := by
    refine RtInv.inv_frame' hF1 (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · right; exact ⟨_, hhdr, by simp only; omega, by simp only; omega⟩
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  have hsh1 : SliceObj B M1 (s.mem.readLE ((s.regs 2).toNat + 8) 8) rs :=
    sliceObj_len0 hsh hF1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega) hlen0
  refine ReachesRet.call (hput L b rs) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩,
    ?_, ?_, hrs, ?_, ?_, ?_, ?_, ?_⟩ ?_
  all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40]
  case refine_2 => omega
  case refine_3 => omega
  case refine_4 => omega
  case refine_5 =>
    rw [← hM1]; simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  case refine_6 => omega
  case refine_7 => rw [← hM1]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hg2
  case refine_8 => rw [hk1 _ _ (by omega) (by omega) (by omega)]; omega
  case refine_9 =>
    simp only [calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, outside_cons, outside_nil, and_true]
    omega
  case refine_11 => rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsh1
  case refine_12 => exact hok
  case refine_13 => exact hinv1
  case refine_14 => exact Nat.zero_le _
  case refine_15 =>
    intro r hr; have := hLs r hr
    simp only [liveWin64, calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, List.cons_append,
      List.nil_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  case refine_16 =>
    intro r hr
    simp only [liveWin64, calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  all_goals first | (janus64_simp; done) | decide | rfl | skip
  intro s2 hpc2 ⟨r, x2, y2, fl, m, zh, kr, hs2, hMF, hLF, hNew, hinv2⟩
  subst hs2
  simp only [calleeStack64, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40] at hMF
  have hkm : ∀ a, ((s.regs 4).toNat - 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 8) → m.readLE a 8 = M1.readLE a 8 :=
    fun a ha => hMF.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩)
  have r8 : m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hkm _ (by omega), ← hM1, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  have r0 : m.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hkm _ (by omega), hk1 _ _ (by omega) (by omega) (by omega)]
  have hra2 : retAddrOf
      { regs := setRegF (setRegF (setRegF (setRegF (setRegF s.regs 0 12107072#64) 1
                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 2) + 8) 8))) 3 7434400#64)
            4 (s.regs 4 - 40#64)) 5 (s.regs 4 - 8#64),
        rip := 4789440#64, flags := (subFlags (s.regs 4 - 8#64) (24#64) false).snd, xmm := s.xmm, mem := M1,
        ymmHi := s.ymmHi, fsBase := s.fsBase, df := s.df, mxcsr := s.mxcsr, x87 := s.x87, fpucw := s.fpucw,
        zmmHi := s.zmmHi, kreg := s.kreg : State } = 6191629#64 := by
    simp only [retAddrOf, setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp40, hret]
  rw [hra2]
  janus64_run [r8, r0, hsp40]
  refine ⟨⟨?_, ?_, ?_, ?_, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, MapAmd64.keepABI_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · simp only [MapAmd64.keepX15_apply, ↓reduceIte]
  · refine hF1.trans hMF fun a k ho => ?_
    simp only [stkOf, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1, h2⟩ := ho
    exact ⟨⟨by omega, h2, by omega⟩, hrt, by omega, by omega⟩
  · refine ⟨fun a k hin hws => ?_⟩
    simp only [stkOf, outside_cons, outside_nil, and_true] at hws
    obtain ⟨r0, hr0, i1, i2⟩ := hin
    have := hLs r0 hr0
    simp only [outside_cons, outside_nil, and_true] at this
    rw [hLF.readLE a k ⟨r0, hr0, i1, i2⟩ trivial,
      hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; exact ⟨by omega, hws, by omega⟩)]
  · exact hinv2

end FvModexp.Amd64.Free
