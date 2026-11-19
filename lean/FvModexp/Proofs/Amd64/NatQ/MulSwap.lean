import FvModexp.Proofs.Amd64.NatQ.MulLift
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulSwap.lean — TIGHT COSTS] `nat.mul` (amd64): `m < n` → `return z.mul(stk, y, x)` (natmul.go:21-22)

`mulCall`: a call of `nat.mul` through the SCC's induction hypothesis at its entry `0x5f0840`. `swap2`: from the
self-call's entry (`CALL` at `0x5f0c62` done: `x` stored as the stack argument at `0(SP') .. 0x10(SP')`
= `RSP - 256 .. - 240`, `y` in `SI, R8, R9`, return `0x5f0c67` at `RSP - 264`) through the call to the return
(`MOVQ AX, 0x98(SP)` …, `ADDQ $0xf8, SP; POPQ BP; RET`); `swap`: the entry → that call. `mpre_swap` / `mpost_comm`
swap the operands of `MPre` / `MPost`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

theorem mpre_swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    (h : MPre R b H L W zp zc st xp xl xc yp yl yc s) (hw : mulW64 yl xl ≤ W) :
    MPre R b H L W zp zc st yp yl yc xp xl xc s := by
  obtain ⟨hce, -, hsv, hglb, hty, hops, hstk, hcost, hadx, hinv⟩ := h
  exact ⟨hce, hw, hsv, hglb, hty, hops.swap, hstk, by rw [mulCQ_comm, Nat.add_comm yl xl]; exact hcost, hadx, hinv⟩

theorem mpost_comm {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s s' : State}
    (h : MPost R b H L W zp zc st yp yl yc xp xl xc s s') : MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hfs, hdf, p', l', c', q0, q1, q2, hv, hn, hlc, hll, hc40, L', b', hext, hbud, hinv, hlive, hkind, hfa, hex,
    hsb, hMF, hLF⟩ := h
  have em : natVal s.mem yp yl * natVal s.mem xp xl = natVal s.mem xp xl * natVal s.mem yp yl := Nat.mul_comm _ _
  refine ⟨hfs, hdf, p', l', c', q0, q1, q2, by rw [hv, em], hn, hlc, by omega, hc40, L', b', hext,
    by rw [mulCQ_comm]; exact hbud, hinv, hlive, ?_, hfa, ?_, hsb, hMF, hLF⟩
  · rcases hkind with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, h2, h3⟩
  · intro h1 h2 h3
    obtain ⟨e1, e2, hvz, hF, hLF'⟩ := hex (by omega) h3 h2
    rw [Nat.add_comm yl xl] at hvz hF hLF'
    rw [em] at hvz
    exact ⟨e1, e2, hvz, hF, hLF'⟩

set_option maxRecDepth 20000 in
/-- a call of `nat.mul` through the induction hypothesis at its entry `0x5f0840` -/
theorem mulCall {impl : List Amd64.Segment} {R : RtInv} {n : Nat} (hih : ∀ j, IH impl R H n j) (a : Args)
    {S : State} {ret : W64} {Q : State → Prop} {r : Nat}
    (hpc : S.rip = BitVec.ofNat 64 0x5f0840) (hrd : S.mem.readLE (S.regs 4).toNat 8 = r) (hE : Entry a S)
    (hpre : MPre R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat
      a.a8.toNat a.a9.toNat S)
    (hmu : μl a.a5.toNat a.a8.toNat + 3 < n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 r → Kept S s' →
      MPost R a.b H a.L a.W a.a0.toNat a.a2.toNat a.a3.toNat a.a4.toNat a.a5.toNat a.a6.toNat a.a7.toNat a.a8.toNat
        a.a9.toNat S s' →
      s'.mem.regions = S.mem.regions → ReachesRet (LibMul.program.link impl) ret s' Q) :
    ReachesRet (LibMul.program.link impl) ret S Q := by
  have hS : Summary (LibMul.program.link impl) 0x5f0840 (fun s => preOf R H (.mul, a) s ∧ μ (.mul, a) s < n)
      (postOf R H (.mul, a)) := hih (.mul, a)
  refine ReachesRet.call_regions hS hpc ⟨⟨hE, hpre⟩, hmu⟩ fun s' hr ⟨hk, hq⟩ hrg => K s' ?_ hk hq hrg
  rw [hr, retAddrOf, hrd]

/-- the two bounds of `mul_keeps` for a word `[a, a + 8)`, `sp - 8 ≤ a ≤ sp`, of `swap2`'s caller frame
(small-context `omega`s, kept out of `swap2`'s large context: 18 s → 0) -/
theorem swA {sp S4 a : Nat} (e : S4 = sp - 264) (h : 264 ≤ sp) (ha : sp - 8 ≤ a) : S4 + 88 ≤ a := by omega

theorem swB {sp a : Nat} (ha : a ≤ sp) : a + 8 ≤ sp + 88 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the self-call's entry (operands swapped) to the return of `nat.mul` -/
theorem swap2 (impl : List Amd64.Segment) (R : RtInv) (n : Nat) (ih : ∀ j, IH impl R H n j) {b : Nat}
    {L : List (Nat × Nat)} {W : Nat} {zp zl zc st xp xl xc yp yl yc : BitVec 64} {s : State}
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hpreS : MPre R b H L W zp.toNat zc.toNat st.toNat yp.toNat yl.toNat yc.toNat xp.toNat xl.toNat xc.toNat s)
    (hμ : μl yl.toNat xl.toNat + 3 < n) (hw1 : mulW64 yl.toNat xl.toNat + 264 ≤ W)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hdf0 : s.df = false) (hx150 : s.xmm 15 = 0#128)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 0x5f0840) (hsp : S.regs 4 = s.regs 4 - 264#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hfs : S.fsBase = s.fsBase)
    (hdf : S.df = false) (hx15 : S.xmm 15 = 0#128)
    (r0 : S.regs 0 = zp) (r3 : S.regs 3 = zl) (r1 : S.regs 1 = zc) (r7 : S.regs 7 = st) (r6 : S.regs 6 = yp)
    (r8 : S.regs 8 = yl) (r9 : S.regs 9 = yc)
    (mx1 : S.mem.readLE ((s.regs 4).toNat - 256) 8 = xp.toNat)
    (mx2 : S.mem.readLE ((s.regs 4).toNat - 248) 8 = xl.toNat)
    (mx3 : S.mem.readLE ((s.regs 4).toNat - 240) 8 = xc.toNat)
    (hF : MemFrame s.mem S.mem (win s W 88)) (hreg : S.mem.regions = s.mem.regions)
    (mret : S.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0c67)
    (mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
      Kept s s' ∧ MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb0, ha0, hw0⟩, hal0, -⟩, -⟩ := hpre'
  simp only [regSP] at hb0 ha0 hw0
  have hW : 4608 + 264 ≤ W := by have := mulW64_ge yl.toNat xl.toNat; omega
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 264 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hpre1 := mpre_down hpreS (f := 264) (W1 := W - 264) hsp' h14 hfs hF hreg (by omega) (by omega) (by omega)
  refine mulCall ih ⟨b, L, W - 264, zp, zl, zc, st, yp, yl, yc, xp, xl, xc⟩ (r := 0x5f0c67) hpc
    (by rw [hsp']; exact mret)
    ⟨by rw [hsp', mret]; decide, hx15, hdf, r0, r3, r1, r7, r6, r8, r9,
      by rw [hsp', show (s.regs 4).toNat - 264 + 8 = (s.regs 4).toNat - 256 by omega]; exact mx1,
      by rw [hsp', show (s.regs 4).toNat - 264 + 16 = (s.regs 4).toNat - 248 by omega]; exact mx2,
      by rw [hsp', show (s.regs 4).toNat - 264 + 24 = (s.regs 4).toNat - 240 by omega]; exact mx3⟩
    hpre1 hμ (fun s' hr ⟨e4, e5, e14, e15⟩ hq hrg => ?_)
  have hMF : MemFrame S.mem s'.mem (R.rt ++ win S (W - 264) 88 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)] ++
      stkWs S.mem st.toNat) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, -⟩ := hq; exact h
  have hz' : Outside zp.toNat (8 * zc.toNat) (win s W 88) := hpre.2.2.2.2.2.1.2.2.1.2.2.1
  have hkp := mul_keeps (W1 := W - 264) (f := 264) (S1 := S) (m2 := s'.mem) hpreS hsp' (by omega) hF hz' hMF
  have h264 : 264 ≤ (s.regs 4).toNat := Nat.le_trans (Nat.le_trans (by decide) hW) hb0
  have q1 : s'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hkp _ _ (swA hsp' h264 (Nat.sub_le _ _)) (swB (Nat.le_refl _))]; exact mra
  have q2 : s'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hkp _ _ (swA hsp' h264 (Nat.le_refl _)) (swB (Nat.sub_le _ _))]; exact mbp
  have hacc : s'.mem.accessible ((s.regs 4).toNat - 256) 264 true = true := by
    rw [hMF.accessible, hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsp2 : s'.regs 4 = s.regs 4 - 256#64 := by
    rw [e4, hsp]; apply BitVec.eq_of_toNat_eq
    have e8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, e8]; omega
  have qfs : s'.fsBase = s.fsBase := hq.1.trans hfs
  have qdf : s'.df = s.df := hq.2.1.trans (hdf.trans hdf0.symm)
  janus64_run [q1, q2, hsp2, e5, h5, BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, mpost_comm (mpost_up hpreS (f := 264) (W1 := W - 264) hsp' (by omega) h14 hfs (hdf.trans hdf0.symm)
    hF hq ?qF ?_ ?_ ?_ ?_ ?_)⟩
  case qF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact qfs | exact qdf | (rw [e14, h14]) | (rw [e15, hx15, hx150]) | exact hx150.symm | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`m < n`**: the entry → the self-call (operands swapped) → the return -/
theorem swap (impl : List Amd64.Segment) (R : RtInv) (n : Nat) (ih : ∀ j, IH impl R H n j) (b : Nat)
    (L : List (Nat × Nat)) (W : Nat) (zp zl zc st xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 0x5f0840)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hy1 : s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat) (hy2 : s.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat)
    (hy3 : s.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat)
    (hpre : MPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s)
    (hμ : μl xl.toNat yl.toNat + 3 = n) (hlt : xl.toNat < yl.toNat) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) s fun s' =>
      Kept s s' ∧ MPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat yp.toNat yl.toNat yc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -⟩, hmw, -, -, -,
    ⟨⟨-, -, hxl12, -⟩, ⟨-, -, hyl12, -⟩, -⟩, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW : 4608 ≤ W := Nat.le_trans (mulW64_ge _ _) hmw
  have hsw := mulW64_swap hlt
  have hpreS := mpre_swap hpre (by omega)
  janus64_run [hy1, hy2, hy3, toInt_small xl (by omega), toInt_small yl (by omega), Int.ofNat_lt, hlt,
    BitVec.msb_eq_decide] until [0x5f0840]
  refine swap2 impl R n ih (zl := zl) hpre hpreS (by rw [← hμ]; exact μ_swap hlt) (by omega) hra hdf hx15 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?_ ?_ ?_ ?_
  case qF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact hx15 | omega

end FvModexp.Amd64.Q.NatMul
