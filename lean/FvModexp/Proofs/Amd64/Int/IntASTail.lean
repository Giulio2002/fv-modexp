import FvModexp.Proofs.Amd64.Int.IntASWb

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): from the return of the `nat` call to `RET`

The three call sites (`+0x56` after `nat.add`, `+0xf4` / `+0x15d` after `nat.sub(x, y)` / `nat.sub(y, x)`; `Sub` =
`Add` + `0x1e0`) continue with the same code: `MOVQ 0x60(SP), DX` (= z), `z.abs.len, cap` stores, the write-barrier
flag test (barrier on: `MOVQ 0x8(DX), CX`, `CALL gcWriteBarrier2`, the buffer stores at `R11`), `z.abs.ptr` store, the
sign byte `0x4f(SP)` (`+0x15d`: `XORL $1`), `z.neg = len ≠ 0 & neg`, `ADDQ $0x50, SP; POPQ BP; RET`. Twin of the arm64
`IntAS.tail`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.IntAS

/-- registers kept by the call (callee-saved part of the Go ABI; as `StackNat.RegsOK`) -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

/-- the final sign byte (amd64 `SETNE BL; ANDL CX, BX`): `(len ≠ 0) & neg` -/
theorem nbA (l' nx : Nat) (h : nx ≤ 1) :
    ((BitVec.toNat (BitVec.ofNat 64 l' &&& 18446744073709551360#64 |||
        BitVec.setWidth 64 (if l' = 0 then 0#8 else 1#8)) % 4294967296 &&& nx % 4294967296) % 256) =
      if l' = 0 then 0 else nx := by
  have key : ∀ W : BitVec 64, W.toNat % 2 = 1 →
      (W.toNat % 4294967296 &&& 1 % 4294967296) % 256 = 1 := by
    intro W hW
    rw [show (1 : Nat) % 4294967296 = 1 from rfl, Nat.and_one_is_mod]
    omega
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl
  · simp
  · by_cases hl : l' = 0
    · subst hl; decide
    · simp only [hl, ↓reduceIte]
      refine key _ ?_
      rw [BitVec.toNat_or, BitVec.toNat_and]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.or_mod_two_eq_one]
      exact Or.inr (by decide)

/-- the final sign byte after `XORL $1, CX` (the `nat.sub(y, x)` site): `(len ≠ 0) & (neg ^ 1)` -/
theorem nbAC (l' nx : Nat) (h : nx ≤ 1) :
    ((BitVec.toNat (BitVec.ofNat 64 l' &&& 18446744073709551360#64 |||
        BitVec.setWidth 64 (if l' = 0 then 0#8 else 1#8)) % 4294967296 &&&
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 nx))) ^^^ 1#32).toNat %
        4294967296) % 256) =
      if l' = 0 then 0 else 1 - nx := by
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl
  · rw [show (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 0))) ^^^ 1#32).toNat = 1
      from by decide]
    exact nbA l' 1 (by omega)
  · rw [show (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 1))) ^^^ 1#32).toNat = 0
      from by decide]
    exact nbA l' 0 (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (off : Nat) (hoff : off = 0x56 ∨ off = 0xf4 ∨ off = 0x15d)
    (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State)
    (nb V cost p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) (hpc : S.rip = BitVec.ofNat 64 (entry sub + off))
    (hnb : nb = if off = 0x15d then 1 - hNeg s.mem x else hNeg s.mem x)
    (hra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ReachesRet (LibIntAS.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Post sub R b L z x y s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -, -⟩, hsv, -, hx, -, hza, hz48, hzo, hzH, -, -,
    hzwb, -, -, -, -, -, -, hwbf, -, -⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hnx : hNeg s.mem x ≤ 1 := hx.1
  clear hx
  have hsp := h.sp; have h14 := h.g; have hfs := h.fs; have hdf := h.df; have hx15 := h.x15; have h5 := h.bp
  have h0 := h.r0; have h3 := h.r3; have h1 := h.r1
  have hc40 := h.c40; have hlc := h.lc; have hp64 := h.p64
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  unfold Apart at hzwb
  have hwbv : wbA = 12283968 := rfl
  rw [hwbv] at hzwb hwbf
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hzs : S.mem.readLE ((s.regs 4).toNat - 88 + 96) 8 = z := by
    rw [show (s.regs 4).toNat - 88 + 96 = (s.regs 4).toNat + 8 by omega]; exact h.zs
  have hng : S.mem.readLE ((s.regs 4).toNat - 88 + 79) 1 = hNeg s.mem x := by
    rw [show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]; exact h.ng
  have hmbp : S.mem.readLE ((s.regs 4).toNat - 88 + 80) 8 = (s.regs 5).toNat := by
    rw [show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]; exact h.mbp
  have hra : S.mem.readLE ((s.regs 4).toNat - 88 + 88) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]; exact h.ra
  have hzaS : S.mem.accessible z 32 true = true := by rw [h.mf.accessible]; exact hza
  have hwbS : S.mem.accessible 12283968 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4536) (4536 + 32) true = true := by rw [h.mf.accessible]; exact hw
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  have hLW : LiveSep L1 [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] :=
    liveSep_ext h.ext (fun r hr => by
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
  rcases hoff with rfl | rfl | rfl <;> cases sub <;>
    simp only [entry, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff] at hpc hnb <;>
    janus64_run [hsp, h88, hzs, hng, hmbp, hra, h.zs, h.ng, h.mbp, h.ra, hzaS, hwbS] until [cA "runtime.gcWriteBarrier2"]
  · (
      refine ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14], hx15⟩,
        post_of h (lo := (s.regs 4).toNat - 4192) (hi := (s.regs 4).toNat - 88) (by omega) (by omega)
          (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _ hfs rfl
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
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
            exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) (inv_hdr h)
      · exact hLW
      · exact hWR
      intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
      subst hs2
      try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
      try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
      obtain ⟨hb8a, hb8b, hbuf64, hbz, hbS, hm87, hmbp2, hra2, hm16, hmz, hmS⟩ := wb_reads h _ hfr2 hlf2 hsl hapL
      have hpB := Box.mk (wb_post h _ hfr2 hlf2 hsl hapL hinvS)
      clear hfr2 hlf2 hsl hapL hapW hinvS
      have hra3 : m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [← hra2, show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
      have hmbp3 : m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [← hmbp2, show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
      have hm873 : m'.readLE ((s.regs 4).toNat - 9) 1 = hNeg s.mem x := by
        rw [← hm87, show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
      janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hm87, hmbp2, hra2, hra3, hmbp3, hm873, hm16, hmz, hmS]
      obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
      exact ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14], rfl⟩,
        post_of h (by omega) (by omega) hMw hLw hIw _ hfs rfl (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14], hx15⟩,
        post_of h (lo := (s.regs 4).toNat - 4192) (hi := (s.regs 4).toNat - 88) (by omega) (by omega)
          (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _ hfs rfl
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
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
            exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) (inv_hdr h)
      · exact hLW
      · exact hWR
      intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
      subst hs2
      try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
      try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
      obtain ⟨hb8a, hb8b, hbuf64, hbz, hbS, hm87, hmbp2, hra2, hm16, hmz, hmS⟩ := wb_reads h _ hfr2 hlf2 hsl hapL
      have hpB := Box.mk (wb_post h _ hfr2 hlf2 hsl hapL hinvS)
      clear hfr2 hlf2 hsl hapL hapW hinvS
      have hra3 : m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [← hra2, show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
      have hmbp3 : m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [← hmbp2, show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
      have hm873 : m'.readLE ((s.regs 4).toNat - 9) 1 = hNeg s.mem x := by
        rw [← hm87, show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
      janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hm87, hmbp2, hra2, hra3, hmbp3, hm873, hm16, hmz, hmS]
      obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
      exact ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14], rfl⟩,
        post_of h (by omega) (by omega) hMw hLw hIw _ hfs rfl (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14], hx15⟩,
        post_of h (lo := (s.regs 4).toNat - 4192) (hi := (s.regs 4).toNat - 88) (by omega) (by omega)
          (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _ hfs rfl
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
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
            exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) (inv_hdr h)
      · exact hLW
      · exact hWR
      intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
      subst hs2
      try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
      try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
      obtain ⟨hb8a, hb8b, hbuf64, hbz, hbS, hm87, hmbp2, hra2, hm16, hmz, hmS⟩ := wb_reads h _ hfr2 hlf2 hsl hapL
      have hpB := Box.mk (wb_post h _ hfr2 hlf2 hsl hapL hinvS)
      clear hfr2 hlf2 hsl hapL hapW hinvS
      have hra3 : m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [← hra2, show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
      have hmbp3 : m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [← hmbp2, show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
      have hm873 : m'.readLE ((s.regs 4).toNat - 9) 1 = hNeg s.mem x := by
        rw [← hm87, show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
      janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hm87, hmbp2, hra2, hra3, hmbp3, hm873, hm16, hmz, hmS]
      obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
      exact ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14], rfl⟩,
        post_of h (by omega) (by omega) hMw hLw hIw _ hfs rfl (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14], hx15⟩,
        post_of h (lo := (s.regs 4).toNat - 4192) (hi := (s.regs 4).toNat - 88) (by omega) (by omega)
          (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _ hfs rfl
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
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
            exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) (inv_hdr h)
      · exact hLW
      · exact hWR
      intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
      subst hs2
      try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
      try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
      obtain ⟨hb8a, hb8b, hbuf64, hbz, hbS, hm87, hmbp2, hra2, hm16, hmz, hmS⟩ := wb_reads h _ hfr2 hlf2 hsl hapL
      have hpB := Box.mk (wb_post h _ hfr2 hlf2 hsl hapL hinvS)
      clear hfr2 hlf2 hsl hapL hapW hinvS
      have hra3 : m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [← hra2, show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
      have hmbp3 : m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [← hmbp2, show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
      have hm873 : m'.readLE ((s.regs 4).toNat - 9) 1 = hNeg s.mem x := by
        rw [← hm87, show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
      janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hm87, hmbp2, hra2, hra3, hmbp3, hm873, hm16, hmz, hmS]
      obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
      exact ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14], rfl⟩,
        post_of h (by omega) (by omega) hMw hLw hIw _ hfs rfl (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14], hx15⟩,
        post_of h (lo := (s.regs 4).toNat - 4192) (hi := (s.regs 4).toNat - 88) (by omega) (by omega)
          (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _ hfs rfl
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
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
            exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) (inv_hdr h)
      · exact hLW
      · exact hWR
      intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
      subst hs2
      try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
      try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
      obtain ⟨hb8a, hb8b, hbuf64, hbz, hbS, hm87, hmbp2, hra2, hm16, hmz, hmS⟩ := wb_reads h _ hfr2 hlf2 hsl hapL
      have hpB := Box.mk (wb_post h _ hfr2 hlf2 hsl hapL hinvS)
      clear hfr2 hlf2 hsl hapL hapW hinvS
      have hra3 : m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [← hra2, show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
      have hmbp3 : m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [← hmbp2, show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
      have hm873 : m'.readLE ((s.regs 4).toNat - 9) 1 = hNeg s.mem x := by
        rw [← hm87, show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
      janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hm87, hmbp2, hra2, hra3, hmbp3, hm873, hm16, hmz, hmS]
      obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
      exact ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14], rfl⟩,
        post_of h (by omega) (by omega) hMw hLw hIw _ hfs rfl (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14], hx15⟩,
        post_of h (lo := (s.regs 4).toNat - 4192) (hi := (s.regs 4).toNat - 88) (by omega) (by omega)
          (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (inv_hdr h) _ hfs rfl
          (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)
  · (
      refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hsv.2.2.2.2.2.1 [2], ?_, ?_, ?_⟩ ?_
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
            exact Or.inl (hout.of_sub (by simp only; omega) (by simp only; omega))) (inv_hdr h)
      · exact hLW
      · exact hWR
      intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
      subst hs2
      try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
      try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
      obtain ⟨hb8a, hb8b, hbuf64, hbz, hbS, hm87, hmbp2, hra2, hm16, hmz, hmS⟩ := wb_reads h _ hfr2 hlf2 hsl hapL
      have hpB := Box.mk (wb_post h _ hfr2 hlf2 hsl hapL hinvS)
      clear hfr2 hlf2 hsl hapL hapW hinvS
      have hra3 : m'.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [← hra2, show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]
      have hmbp3 : m'.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [← hmbp2, show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]
      have hm873 : m'.readLE ((s.regs 4).toNat - 9) 1 = hNeg s.mem x := by
        rw [← hm87, show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]
      janus64_run [hsp2, h88, hb8a, hb8b, hbuf64, hm87, hmbp2, hra2, hra3, hmbp3, hm873, hm16, hmz, hmS]
      obtain ⟨hMw, hLw, hIw⟩ := hpB.h p' (Arm64.Memory.readLE S.mem (z + 8) 8)
      exact ⟨⟨by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl, by simp only [setRegF_apply, ↓reduceIte],
          by simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, h14], rfl⟩,
        post_of h (by omega) (by omega) hMw hLw hIw _ hfs rfl (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) _
          (by subst hnb; first | exact nbA _ _ hnx | exact nbAC _ _ hnx) rfl⟩)

end FvModexp.Amd64.IntAS
