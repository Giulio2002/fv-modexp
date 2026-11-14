import FvModexp.Proofs.Amd64.Exp.NCallP
import FvModexp.Proofs.Amd64.Exp.NEpi
import FvModexp.Proofs.Amd64.Exp.CallW

/-!
# `nat.expNN` (amd64): a call of a `CPostG` callee (`rem`, `expNNSlow`, `expNNOdd`, `expNNPowerOfTwo`) to the return
(agent expmc s71; twin of `Arm64.ExpN.callC`)

`callC`: from the callee entry `S` (`RSP = sp + 0x388`, `[RSP]` = a return point; callee summary on `onlySegments ns`,
`ns ⊆ LibN.names` without `nat.expNN`): the call, the shared epilogue (`EpiK`), the post (`post_call`). `raN`: the five
return points are return addresses of such callee programs; `keepS`: expNN's slots `[sp + 0x3f8, sp + 0x510)` (the
defer flag bytes, the closure record / pointer, the saved `BP`, the return address) survive the callee.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpN

/-- an `Ensures` on `(Extracted.program.onlySegments ns).link impl` (`ns ⊆ LibN.names`) as a `Summary` of
`LibN.program.link impl` -/
theorem hypSumN {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibN.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 args ∧ s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  have hS := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hlen (A64.codeIn_restrict_mono64 hap hns)
  rw [← LibN.eq_only] at hS
  exact hS

theorem seg11_name : Extracted.seg11.name = fn := by decide

set_option maxRecDepth 20000 in
/-- the callee return points inside `nat.expNN` (`seg11`, base `0x5e6fa0`) -/
theorem raN (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) {r : Nat} (hr : RetPt r) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) r := by
  have hm : Extracted.seg11 ∈ Extracted.program.segments := by
    simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]
  have hn' : ns.contains Extracted.seg11.name = false := by rw [seg11_name]; exact hn
  have h := fun (i : Nat) (hi : i < Extracted.seg11.bytes.length) (hu : 0x5e6fa0 + i < 2 ^ 47) => by
    have := CallW.retAddr_restrict hap hm hn' i hi (by simpa only [Extracted.seg11] using hu)
    simpa only [Extracted.seg11] using this
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h 0x40f (by decide) (by decide)
  · exact h 0x5df (by decide) (by decide)
  · exact h 0x685 (by decide) (by decide)
  · exact h 0x8c5 (by decide) (by decide)
  · exact h 0x957 (by decide) (by decide)

set_option maxRecDepth 20000 in
/-- expNN's slots `[sp + 0x3f8, sp + 0x510)` survive a callee entered with `RSP = sp + 0x388` (window
`win S stk 112`) -/
theorem keepS {R : RtInv} {L : List (Nat × Nat)} {stk sp K zp zc zq zcq st : Nat} {M M' : Janus.Arm64.Memory}
    {S : State} (hSsp : (S.regs 4).toNat = sp + 0x388) (hstk : stk ≤ K + 0x388) (hK : K ≤ sp)
    (hrt : Outside (sp - K) (K + 0x510) R.rt) (hzq : ZArg R L sp K zp zc zq zcq)
    (hstw : Apart st 24 (sp - K) (K + 0x510))
    (harr : 0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - K) (K + 0x510))
    (hc0 : stCap M st = 0 → stW M st = 0) (hlc : stLen M st ≤ stCap M st)
    (hF : MemFrame M M' (R.rt ++ win S stk 112 ++ [(zq, zq + 8 * zcq)] ++ ExpHyp.stWs M st))
    {a k : Nat} (hak : sp + 0x3f8 ≤ a ∧ a + k ≤ sp + 0x510) :
    M'.readLE a k = M.readLE a k := by
  refine Janus.Arm64.Memory.readLE_congr fun i hi => ?_
  have h := hF.readLE (a + i) 1 ?_
  · simp only [Janus.Arm64.Memory.readLE_one] at h; exact BitVec.eq_of_toNat_eq h
  have hrt1 : Outside (a + i) 1 R.rt := hrt.of_sub (by omega) (by omega)
  simp only [ExpHyp.stWs, stkWs, win, hSsp, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨⟨hrt1, by omega⟩, ?_⟩, by unfold Apart at hstw; omega, ?_⟩
  · rcases hzq with ⟨h0, -⟩ | ⟨e1, e2, hzw⟩ | ⟨hin, -⟩
    · rw [h0]; omega
    · rw [e1, e2]; unfold Apart at hzw; omega
    · have := out_inR2 hrt1 hin; omega
  · rcases Nat.eq_zero_or_pos (stCap M st) with h0 | h0
    · have := hc0 h0; rw [this, h0]; omega
    · have := harr h0; unfold Apart at this; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the call of a `CPostG` callee from its entry `S` to expNN's return (`Post`) -/
theorem callC (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hnf : ns.contains fn = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
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
    {f : String} {r : Nat} (hr : RetPt r) {args : List W64} (hlen : args.length ≤ numIntRegs)
    {P : State → Prop} {Q : State → State → Prop}
    (hE : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args P Q)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program f)) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388))
    (hra : S.mem.readLE (sp + 0x388) 8 = r) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hargs : ArgsFrom64 S 0 args) (hPS : P S)
    (hQ : ∀ s', Q S s' → s'.fsBase = S.fsBase ∧ s'.df = S.df ∧ CPostG R b1 L1 stk 112 zq zcq st v cst S s')
    (harr : 0 < stCap S.mem st → Apart (stW S.mem st) (8 * stCap S.mem st) (sp - K) (K + 0x510))
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0) (hlc : stLen S.mem st ≤ stCap S.mem st)
    (hacc : S.mem.accessible (sp + 0x390) 0x110 true = true) (hbp : S.mem.readLE (sp + 0x490) 8 = bp)
    (hrv : S.mem.readLE (sp + 0x498) 8 = ret0) {M0 : Janus.Arm64.Memory} (hsl : SlotEq S.mem M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hS := hypSumN hap hns hlen hE
  have hSs : (S.regs 4).toNat = sp + 0x388 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hrt : Outside (sp - K) (K + 0x510) R.rt := by
    have := hrw _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 0x510 - (sp - K) = K + 0x510 by omega] at this
  refine Reaches.call_regions (hS.withExit hret) hpc ⟨?_, hx15, hargs, hdf, hPS⟩
    (fun s' hr' ⟨⟨e4, e5, e14, ex15⟩, hq⟩ hrg' => ?_)
  · rw [hSs, hra]; exact raN impl hap hnf hr
  obtain ⟨hfs', hdf', hq'⟩ := hQ s' hq
  have hq2 := hq'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hFq, -⟩ := hq2
  have kp := fun {a k : Nat} (h : sp + 0x3f8 ≤ a ∧ a + k ≤ sp + 0x510) =>
    keepS hSs hstk hK hrt hzq hstw harr hc0 hlc hFq h
  have hrip : s'.rip = BitVec.ofNat 64 r := by rw [hr', retAddrOf_eq, hSs, hra]
  have hsp' : s'.regs 4 = BitVec.ofNat 64 (sp + 0x498 - 0x108) := by
    rw [e4, hSsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  refine hEk r s' hr hrip hsp' e14 (by rw [hFq.accessible, show sp + 0x498 - 0x108 = sp + 0x390 by omega]; exact hacc)
    (by rw [show sp + 0x498 - 8 = sp + 0x490 by omega, kp ⟨by omega, by omega⟩]; exact hbp)
    (by rw [kp ⟨by omega, by omega⟩]; exact hrv)
    (hsl.of_rd fun a k hs => kp (by unfold Slot at hs; omega))
    fun s'' f8 _ f0 f3 f1 ffs fdf _ => post_call hs hK hLs hrw hsok hstw hF0 hLF0 hx1 hb1 hzq hSs hstk h14 hv hC hq'
      (by rw [show sp + 0x498 - 0x58 = sp + 0x440 by omega, show sp + 0x498 - 0x40 = sp + 0x458 by omega] at f8
          exact f8) f0 f3 f1 (ffs.trans (hfs'.trans hfsS)) (fdf.trans (hdf'.trans hdfS))

end FvModexp.Amd64.ExpN
