import FvModexp.Proofs.Amd64.Exp.NCall
import FvModexp.Proofs.Amd64.Exp.NLift

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): the call of `expNNEven` (a `Summary` of `LibNE`) to expNN's return (agent expmc s73)

`callCE` = `NCall.callC` on `LibNE` for a callee given as a `Summary` of `LibNE.program.link impl` (asm's
`ExpEven.EvenSum`, the recursive pair's own form: no return-address condition); the epilogue `EpiK` is on `LibN` and
is lifted (`liftNE`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the call of a `CPostG` callee given as a `Summary` of `LibNE` (`expNNEven`) from its entry `S` to expNN's return
(`Post`); the epilogue `EpiK` (on `LibN`) is lifted by `liftNE` -/
theorem callCE (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD : Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n bp : Nat} {s S : State}
    (hs : (s.regs 4).toNat = sp + 0x498) (hK : K ≤ sp) (hsp1 : 0x110 ≤ sp + 0x498)
    (hsp2 : sp + 0x510 ≤ 2 ^ 48)
    (hLs : LiveSep L [(sp - K, sp + 0x510)]) (hrw : LiveSep [(sp - K, sp + 0x510)] R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 0x510))
    (hF0 : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF0 : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} {b1 zq zcq stk v cst mk : Nat}
    (hx1 : LiveExt R L L1) (hb1 : b - mk ≤ b1) (hzq : ZArg R L sp K zp zc zq zcq)
    (hstk : stk ≤ K + 0x388) (h14 : S.regs 14 = s.regs 14) (hfsS : S.fsBase = s.fsBase) (hdfS : S.df = s.df)
    (hv : v = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n)
    (hC : mk + cst ≤ NCost costD costR costS costP xl yl n (stLen s.mem st) (Nat.log2 (natVal s.mem mp n)))
    {e r : Nat} (hr : RetPt r) {P : State → Prop} {Q : State → State → Prop}
    (hS : Summary (LibNE.program.link impl) e P Q)
    (hpc : S.rip = BitVec.ofNat 64 e) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388))
    (hra : S.mem.readLE (sp + 0x388) 8 = r) (hx15 : S.xmm 15 = 0) (hPS : P S)
    (hQ : ∀ s', Q S s' → (s'.regs 4 = S.regs 4 + 8 ∧ s'.regs 14 = S.regs 14 ∧ s'.xmm 15 = S.xmm 15) ∧ s'.fsBase = S.fsBase ∧ s'.df = S.df ∧ CPostG R b1 L1 stk 112 zq zcq st v cst S s')
    (harr : 0 < stCap S.mem st → Apart (stW S.mem st) (8 * stCap S.mem st) (sp - K) (K + 0x510))
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0) (hlc : stLen S.mem st ≤ stCap S.mem st)
    (hacc : S.mem.accessible (sp + 0x390) 0x110 true = true) (hbp : S.mem.readLE (sp + 0x490) 8 = bp)
    (hrv : S.mem.readLE (sp + 0x498) 8 = ret0) {M0 : Janus.Arm64.Memory} (hsl : SlotEq S.mem M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hSs : (S.regs 4).toNat = sp + 0x388 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hrt : Outside (sp - K) (K + 0x510) R.rt := by
    have := hrw _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 0x510 - (sp - K) = K + 0x510 by omega] at this
  refine Reaches.call_regions (hS.withExit hret) hpc hPS (fun s' hr' hq hrg' => ?_)
  obtain ⟨⟨e4, e14, ex15⟩, hfs', hdf', hq'⟩ := hQ s' hq
  have hq2 := hq'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hFq, -⟩ := hq2
  have kp := fun {a k : Nat} (h : sp + 0x3f8 ≤ a ∧ a + k ≤ sp + 0x510) =>
    keepS hSs hstk hK hrt hzq hstw harr hc0 hlc hFq h
  have hrip : s'.rip = BitVec.ofNat 64 r := by rw [hr', retAddrOf_eq, hSs, hra]
  have hsp' : s'.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := by
    rw [e4, hSsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  refine liftNE impl hap <| hEk r s' hr hrip hsp' e14 (ex15.trans hx15) (by rw [hFq.accessible, show sp + 0x498 - 0x108 = sp + 0x390 by omega]; exact hacc)
    (by rw [show sp + 0x498 - 8 = sp + 0x490 by omega, kp ⟨by omega, by omega⟩]; exact hbp)
    (by rw [kp ⟨by omega, by omega⟩]; exact hrv)
    (hsl.of_rd fun a k hs => kp (by unfold Slot at hs; omega))
    fun s'' f8 _ f0 f3 f1 ffs fdf _ => post_call hs hK hLs hrw hsok hstw hF0 hLF0 hx1 hb1 hzq hSs hstk h14 hv hC hq'
      (by rw [show sp + 0x498 - 0x58 = sp + 0x440 by omega, show sp + 0x498 - 0x40 = sp + 0x458 by omega] at f8
          exact f8) f0 f3 f1 (ffs.trans (hfs'.trans hfsS)) (fdf.trans (hdf'.trans hdfS))

end FvModexp.Amd64.ExpN
