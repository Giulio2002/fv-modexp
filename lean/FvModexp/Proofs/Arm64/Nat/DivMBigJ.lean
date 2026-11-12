import FvModexp.Proofs.Arm64.Nat.DivMBig

set_option autoImplicit false

/-!
# `nat.div` (arm64), `stk == nil`, `z = nil`, `z2 = u`, `u ≥ v`: from the join after `getStack()` to the return

`joinBig`: at `joinA` (`X1` = the new stack `d`, `NewStk` at the current memory): the defer record and the argument
reloads (`joinD`), then `bigCallM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.DivNil

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem joinBig (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc)
    (hput : PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {b : Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl) (hu64 : u < 2 ^ 64)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    {L1 : List (Nat × Nat)} {b1 d : Nat} (S : State) (hN : NewStk R L L1 b b1 (s.regs 28).toNat S.mem d)
    (hF : MemFrame s.mem S.mem (R.rt ++ winA s 41504 112)) (hLF : LiveFrame s.mem S.mem L [])
    (hreg : S.mem.regions = s.mem.regions)
    (hpc : S.pc = BitVec.ofNat 64 joinA) (hsp : S.sp = s.sp - 240#64) (h1 : S.regs 1 = BitVec.ofNat 64 d)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 248#64) (h18 : S.regs 18 = s.regs 18)
    (mlr : S.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (mfp : S.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat)
    (m1 : S.mem.readLE (s.sp.toNat + 8) 8 = 0) (m2 : S.mem.readLE (s.sp.toNat + 16) 8 = 0)
    (m3 : S.mem.readLE (s.sp.toNat + 24) 8 = 0) (m5 : S.mem.readLE (s.sp.toNat + 40) 8 = u)
    (m6 : S.mem.readLE (s.sp.toNat + 48) 8 = ul) (m7 : S.mem.readLE (s.sp.toNat + 56) 8 = uc)
    (m8 : S.mem.readLE (s.sp.toNat + 64) 8 = u) (m9 : S.mem.readLE (s.sp.toNat + 72) 8 = ul)
    (m10 : S.mem.readLE (s.sp.toNat + 80) 8 = uc) (m11 : S.mem.readLE (s.sp.toNat + 88) 8 = v)
    (m12 : S.mem.readLE (s.sp.toNat + 96) 8 = vl) (m13 : S.mem.readLE (s.sp.toNat + 104) 8 = vc) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hp.ce
  have hwO : Outside (s.sp.toNat - 41504) (41504 + 112) R.rt := hout
  have hd : d < 2 ^ 64 := by have := hN.2.2.2.2.1; omega
  have hSacc : S.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hF.accessible]; exact hw
  have hws : ∀ r ∈ [(s.sp.toNat - 122, s.sp.toNat - 120), (s.sp.toNat - 32, s.sp.toNat - 8)],
      Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals exact hwO.of_sub (by simp only; omega) (by simp only; omega)
  have hLs2 : LiveSep L [(s.sp.toNat - 122, s.sp.toNat - 120), (s.sp.toNat - 32, s.sp.toNat - 8)] := by
    intro r hr
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  have i1 : ∀ a n, (a + n ≤ s.sp.toNat - 122 ∨ s.sp.toNat - 8 ≤ a) →
      (a + n ≤ s.sp.toNat - 32 ∨ s.sp.toNat - 120 ≤ a) → a + n ≤ s.sp.toNat - 32 →
      Outside a n [(s.sp.toNat - 122, s.sp.toNat - 120), (s.sp.toNat - 32, s.sp.toNat - 8)] := by
    intro a n h1 h2 h3; simp only [outside_cons, outside_nil, and_true]; omega
  have o240 := i1 (s.sp.toNat - 240) 8 (by omega) (by omega) (by omega)
  have o248 := i1 (s.sp.toNat - 248) 8 (by omega) (by omega) (by omega)
  refine joinD impl (zp := 0) (zl := 0) (zc := 0) (z2 := u) (z2l := ul) (z2c := uc) (u := u) (ul := ul) (uc := uc)
    (v := v) (vl := vl) (vc := vc) hpc hsp h1 hd hal hb' ha hSacc m1 m2 m3 m5 m6 m7 m8 m9 m10 m11 m12 m13 _
    fun X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 xF xR xfl xdw xst xrc => ?_
  have hNX := NewStk.frame hN xF hws
  have hFX : MemFrame s.mem X.mem (R.rt ++ winA s 41504 112) := hF.trans xF fun a n h => ⟨h, by
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
  have hLFX : LiveFrame s.mem X.mem L [] := hLF.trans (LiveFrame.of_win xF hLs2) fun _ _ h => h
  exact bigCallM impl hap R dc hL hput hp hge hv2 hu64 hl4 hl48 X hNX hFX hLFX (by rw [xR, hreg]) x1 (x2.trans hsp)
    (x3.trans h28) (x4.trans h29) (x5.trans h18) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
    ((xF.readLE _ 8 o240).trans mlr) ((xF.readLE _ 8 o248).trans mfp) xfl xdw xst xrc

end FvModexp.Arm64.NatDiv
