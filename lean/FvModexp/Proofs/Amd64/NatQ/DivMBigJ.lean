import FvModexp.Proofs.Amd64.NatQ.DivMBig

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, `u ≥ v`: from the join point `joinA` (stack `d` in `RBX`) to the return (top s42)

Twin of Arm64/NatQ/DivMBigJ.lean: `joinM` (the defer record, the reloads, `CALL divLarge`) then `bigCallM`, the new
stack's facts carried over the defer-record writes (`NewStk.frame`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem joinBig (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    {b : Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl vc s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl) (hu64 : u < 2 ^ 64)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {L1 : List (Nat × Nat)} {b1 d : Nat} (S : State) (hN : NewStk R L L1 b b1 (s.regs 14).toNat S.mem d)
    (hF : MemFrame s.mem S.mem (R.rt ++ win s 41512 112)) (hLF : LiveFrame s.mem S.mem L [])
    (hreg : S.mem.regions = s.mem.regions)
    (hpc : S.rip = BitVec.ofNat 64 joinA) (hsp : S.regs 4 = s.regs 4 - 232#64) (h3 : S.regs 3 = BitVec.ofNat 64 d)
    (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0#128) (hdf : S.df = false)
    (mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m1 : S.mem.readLE ((s.regs 4).toNat + 56) 8 = 0) (m2 : S.mem.readLE ((s.regs 4).toNat + 64) 8 = 0)
    (m3 : S.mem.readLE ((s.regs 4).toNat + 72) 8 = 0) (m5 : S.mem.readLE ((s.regs 4).toNat + 88) 8 = u)
    (m6 : S.mem.readLE ((s.regs 4).toNat + 96) 8 = ul) (m7 : S.mem.readLE ((s.regs 4).toNat + 104) 8 = uc)
    (m8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = u) (m9 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = ul)
    (m10 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = uc) (m11 : S.mem.readLE ((s.regs 4).toNat + 32) 8 = v)
    (m12 : S.mem.readLE ((s.regs 4).toNat + 40) 8 = vl) (m13 : S.mem.readLE ((s.regs 4).toNat + 48) 8 = vc) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hwO : Outside ((s.regs 4).toNat - 41512) (41512 + 112) R.rt := hout
  have hd : d < 2 ^ 64 := by have := hN.2.2.2.2.1; omega
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hF.accessible]; exact hw
  have hws : ∀ r ∈ [((s.regs 4).toNat - 240, (s.regs 4).toNat - 184),
      ((s.regs 4).toNat - 122, (s.regs 4).toNat - 120), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 8)],
      Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals exact hwO.of_sub (by simp only; omega) (by simp only; omega)
  have hLs2 : LiveSep L [((s.regs 4).toNat - 240, (s.regs 4).toNat - 184),
      ((s.regs 4).toNat - 122, (s.regs 4).toNat - 120), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 8)] := by
    intro r hr
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  have oS : ∀ k, k ≤ 8 → Outside ((s.regs 4).toNat - k) 8 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 184),
      ((s.regs 4).toNat - 122, (s.regs 4).toNat - 120), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 8)] := by
    intro k hk; simp only [outside_cons, outside_nil, and_true]; omega
  refine joinM impl (zp := 0) (zl := 0) (zc := 0) (z2 := u) (z2l := ul) (z2c := uc) (u := u) (ul := ul) (uc := uc)
    (v := v) (vl := vl) (vc := vc) hpc hsp h3 hd hb' ha hSacc m1 m2 m3 m5 m6 m7 m8 m9 m10 m11 m12 m13 _ _
    fun X hX => ?_
  have xF := hX.mf
  have hNX := NewStk.frame hN xF hws
  have hFX : MemFrame s.mem X.mem (R.rt ++ win s 41512 112) := hF.trans xF fun a n h => ⟨h, by
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
  have hLFX : LiveFrame s.mem X.mem L [] := hLF.trans (LiveFrame.of_win xF hLs2) fun _ _ h => h
  have mra' : X.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [← mra]; have := xF.readLE _ 8 (oS 0 (by decide)); simpa only [Nat.sub_zero] using this
  exact bigCallM impl hap R dc hL hput hp hge hv2 hu64 hra hx0 hdf0 X hNX hFX hLFX (by rw [hX.reg, hreg]) hX.pc
    hX.sp (hX.r14.trans h14) (hX.fs.trans hfs) (hX.x15.trans hx15) (hX.df.trans hdf) hX.a0 hX.a3 hX.a1 hX.a7
    hX.a6 hX.a8 hX.a9 hX.rc mra' ((xF.readLE _ 8 (oS 8 (by decide))).trans mbp) hX.by1 hX.dw hX.dd hX.dp hX.i0
    hX.i1 hX.i3 hX.i4

end FvModexp.Amd64.Q.NatDiv
