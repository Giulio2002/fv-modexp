import FvModexp.Proofs.Amd64.NatQ.MulIWb

set_option autoImplicit false

/-!
# [amd64 port (divmc s54) of the Q-form Arm64/NatQ/MulITail.lean — TIGHT COSTS] `(*Int).mul` (amd64): from the return `0x5e2aa6` of the inner `nat.mul` call to `RET` (int.go:201-203)

`MOVQ 0x60(SP), DX` (= z), the `z.abs.len, cap` stores, the write-barrier flag test (on: `MOVQ 0x8(DX), CX`,
`CALL gcWriteBarrier2`, the buffer stores at `R11`), `z.abs.ptr` store, `z.neg = len ≠ 0 && x.neg ≠ y.neg` (the sign
bytes re-read through the spilled `x`, `y` at `0x70(SP)` / `0x78(SP)`: `MOVZX`, `CMPB`, `SETNE`), `ADDQ $0x50, SP;
POPQ BP; RET`. Twin of `IntAS.tail` (amd64) over `IR`; the barrier facts come from `MulIWb`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)

/-- the final sign byte (`MOVZX (x), AX; CMPB AL, (y); SETNE AL`) for a non-zero length -/
theorem nbF_ne {l' nx ny : Nat} (hx : nx ≤ 1) (hy : ny ≤ 1) (hl : l' ≠ 0) :
    (if BitVec.ofNat 8 ny - BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 nx))) = 0#8
      then 0#8 else 1#8).toNat = if l' = 0 then 0 else nx ^^^ ny := by
  simp only [hl, ↓reduceIte]
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl <;> rcases (by omega : ny = 0 ∨ ny = 1) with rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem itail (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibMul.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (W z st x y : Nat) (s : State)
    (p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (h : IR R b H L W z st x y s p' l' c' b1 L1 S) (hpc : S.rip = BitVec.ofNat 64 0x5e2aa6) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' => Kept s s' ∧ IPost R b H L W z st x y s s' := by
  have hW4 := h.w4704
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -, -⟩, -, hsv, -, -, -,
    ⟨hnx1, hxa, hx48, hxo, -⟩, ⟨hny1, hya, hy48, hyo, -⟩, hza, hz48, hzo, -, -, -, hzwb, hzx, hzy, -, hwbf, -⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hsp := h.sp; have h14 := h.g; have hfs := h.fs; have hdf := h.df; have hx15 := h.x15; have h5 := h.bp
  have h0 := h.r0; have h3 := h.r3; have h1 := h.r1
  have hc40 := h.c40; have hlc := h.lc; have hp64 := h.p64; have hra47 := h.hra
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  unfold Apart at hzwb hzx hzy
  have hwbv : wbA = 12283968 := rfl
  rw [hwbv] at hzwb hwbf
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hzs : S.mem.readLE ((s.regs 4).toNat - 88 + 96) 8 = z := by
    rw [show (s.regs 4).toNat - 88 + 96 = (s.regs 4).toNat + 8 by omega]; exact h.zs
  have hxs : S.mem.readLE ((s.regs 4).toNat - 88 + 112) 8 = x := by
    rw [show (s.regs 4).toNat - 88 + 112 = (s.regs 4).toNat + 24 by omega]; exact h.xs
  have hys : S.mem.readLE ((s.regs 4).toNat - 88 + 120) 8 = y := by
    rw [show (s.regs 4).toNat - 88 + 120 = (s.regs 4).toNat + 32 by omega]; exact h.ys
  have hmbp : S.mem.readLE ((s.regs 4).toNat - 88 + 80) 8 = (s.regs 5).toNat := by
    rw [show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]; exact h.mbp
  have hra : S.mem.readLE ((s.regs 4).toNat - 88 + 88) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]; exact h.ra
  have hnx := h.nx; have hny := h.ny
  have hzaS : S.mem.accessible z 32 true = true := by rw [h.mf.accessible]; exact hza
  have hxaS : S.mem.accessible x 32 false = true := by rw [h.mf.accessible]; exact hxa
  have hyaS : S.mem.accessible y 32 false = true := by rw [h.mf.accessible]; exact hya
  have hwbS : S.mem.accessible 12283968 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hwS : S.mem.accessible ((s.regs 4).toNat - W) (W + 40) true = true := by rw [h.mf.accessible]; exact hw
  have hLW : LiveSep L1 [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] :=
    liveSep_extI h.ext (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hout.of_sub (by omega) (by simp only; omega))
  have hWR : LiveSep [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hout.of_sub (by omega) (by simp only; omega)
  have hsp96' : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsp2 : s.regs 4 - 96#64 + 8#64 = s.regs 4 - 88#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsp96', BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hsp, h88, hzs, hxs, hys, hmbp, hra, h.zs, h.xs, h.ys, h.mbp, h.ra, hnx, hny, hzaS, hxaS, hyaS, hwbS,
    hwS] until [cA "runtime.gcWriteBarrier2"]
  · obtain rfl : l' = 0 := by janus_assumption
    refine ⟨⟨?_, ?_, ?_, hx15⟩, ipost_of h (MemFrame.refl _ _) (LiveFrame.refl _ _ _) h.inv_hdr _ 0 (by simp) rfl hfs
      rfl⟩
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14]; try rfl
  · refine ⟨⟨?_, ?_, ?_, hx15⟩, ipost_of h (MemFrame.refl _ _) (LiveFrame.refl _ _ _) h.inv_hdr _ _
      (nbF_ne hnx1 hny1 (by janus_assumption)) rfl hfs rfl⟩
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14]; try rfl
  · refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14]
    · rw [Arm64.Memory.readLE_writeLE_self]; omega
    · omega
    · omega
    · omega
    · simp only [Arm64.Memory.accessible_writeLE]
      exact Arm64.Memory.accessible_mono _ hwS (by omega) (by omega)
    · exact RtInv.inv_frame' (ws := [((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)]) (by janus_frame)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) h.inv_hdr
    · exact hLW
    · exact hWR
    intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
    subst hs2
    try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
    try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
    obtain ⟨hb8a, hb8b, hbuf64, hbz, hbx, hby, hbS, hmx, hmy, hmbp2, hra2, hmxs, hmys, hmz, hmxa, hmya, hmS⟩ :=
      wbm_reads h _ hfr2 hlf2 hsl hapL
    have hpB := IntAS.Box.mk (wbm_post h _ hfr2 hlf2 hsl hapL hinvS)
    clear hfr2 hlf2 hsl hapL hapW hinvS
    have hmbp3 : m'.readLE ((s.regs 4).toNat - 88 + 80) 8 = (s.regs 5).toNat := by
      rw [show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]; exact hmbp2
    have hra3 : m'.readLE ((s.regs 4).toNat - 88 + 88) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]; exact hra2
    have hmxs3 : m'.readLE ((s.regs 4).toNat - 88 + 112) 8 = x := by
      rw [show (s.regs 4).toNat - 88 + 112 = (s.regs 4).toNat + 24 by omega]; exact hmxs
    have hmys3 : m'.readLE ((s.regs 4).toNat - 88 + 120) 8 = y := by
      rw [show (s.regs 4).toNat - 88 + 120 = (s.regs 4).toNat + 32 by omega]; exact hmys
    janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hmx, hmy, hmbp2, hra2, hmxs, hmys, hmbp3, hra3, hmxs3, hmys3, hmz,
      hmxa, hmya, hmS]
    all_goals obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
    · obtain rfl : l' = 0 := by janus_assumption
      refine ⟨⟨?_, ?_, ?_, rfl⟩, ipost_of h hMw hLw hIw _ 0 (by simp) rfl hfs rfl⟩
      all_goals simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14]; try rfl
    · refine ⟨⟨?_, ?_, ?_, rfl⟩, ipost_of h hMw hLw hIw _ _ (nbF_ne hnx1 hny1 (by janus_assumption)) rfl hfs rfl⟩
      all_goals simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14]; try rfl

end FvModexp.Amd64.Q.NatMul
