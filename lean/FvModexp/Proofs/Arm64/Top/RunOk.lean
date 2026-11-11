import FvModexp.Proofs.Arm64.Top.RunPre
import FvModexp.Proofs.Arm64.Top.RunD1All
import FvModexp.Proofs.Arm64.Top.RunD2All
import FvModexp.Proofs.Arm64.Top.RunD3All
import FvModexp.Proofs.Arm64.Top.RunC1
import FvModexp.Proofs.Arm64.Top.RunC2M
import FvModexp.Proofs.Arm64.Top.RunC2E
import FvModexp.Proofs.Arm64.Top.RunCP1
import FvModexp.Proofs.Arm64.Top.RunCP2

/-!
# `Run` (arm64): the success path, composed

From the entry, when the three lengths are at most 1024 (EIP-7823 passes), `Run` returns `(out, nil)` where `out` has
`modLen` bytes whose big-endian value is `resV` (`0` for a zero modulus, else `base ^ exp mod modulus`), or — for
`baseLen = modLen = 0` — the empty output. Composition: `runPre` (headers, lengths, empty case) → `d1`/`d2`/`d3`
(operands) → `c1` (zero modulus) → `c2m` (`base = 1`: `Mod`) / `c2e` (`exp`) → `cp1` → `cp2` (`LeftPadBytes`).
The big callees enter as their interface specs (`RunIface.ModSpec`/`ExpSpec`/`BytesSpec`), the runtime as live contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- A call environment for more stack is one for less (adapted from `NatAdd.callEnv_mono`). -/
theorem callEnv_mono' {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk stk' above : Nat} (hk : stk' ≤ stk)
    (h : CallEnv R L s stk above) : CallEnv R L s stk' above := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := h
  unfold Apart at hga
  refine ⟨⟨hg1, hg2, by omega⟩, ⟨hal, by omega, ha, Memory.accessible_mono _ hw (by omega) (by omega)⟩, hd,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgr, fun r hr => ?_, hro⟩
  have := hLs r hr
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
  omega

/-- The empty output of `baseLen = modLen = 0` is `resV`'s encoding on `0` bytes. -/
theorem resV_zero {s : State} {p len : BitVec 64} (h2 : hdrV s p len 2 = 0) : resV s p len = 0 := by
  have : opV s p len 2 = 0 := by
    simp only [opV, opLen, show ((2 : Nat) = 0) = False by decide, show ((2 : Nat) = 1) = False by decide, if_false, h2]
    rfl
  simp [resV, this]

theorem okB_ge (s : State) (p len : BitVec 64) :
    3 * makeCost 4 + 3 * dCost + allocCost 1024 ≤ okB s p len ∧ 3 * makeCost 4 + allocCost 16 ≤ okB s p len := by
  unfold okB allocCost; omega

set_option maxRecDepth 20000 in
/-- **The success path of `Run` (arm64), on the library program.** -/
theorem okReach (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (stkM aboveM : Nat) (hM : RunIface.ModSpec impl R stkM aboveM) (hE : RunIface.ExpSpec impl R stkM aboveM)
    (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (hs : CallSetup ((LibRun.program.link impl).withExit ret) (segAddr Extracted.program fn) [c, p, len, cp] s)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 624 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 160)
    (hin : InputOK R L c p len cp s) (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
    (hrecv : s.mem.readLE c.toNat 3 = 65793)
    (hglob : RunIface.Globals R s.mem (win s W 40)) (hgL : ApartAll ((s.regs 28).toNat + 16) 8 L)
    (hbB : okB s p len ≤ b)
    (hpass : hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024)
    (Q : Outcome → Prop)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b (okB s p len) L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S')) :
    Reaches ((LibRun.program.link impl).withExit ret) s Q := by
  obtain ⟨hS1, hS2, -, -, hS5, -⟩ := hsv
  have hsv' : RunIface.Serves R := hsv
  have hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n] :=
    fun n hn => hS1 _ _ _ (by unfold makeCap; split <;> omega)
  have hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n] := fun n hn => hS1 _ _ _ (by omega)
  have hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n] := hS2
  have hokM' : ∀ d sr n, n ≤ 1024 → R.ok (cA "runtime.memmove") [d, sr, n] := fun d sr n hn => hS2 _ _ _ (by omega)
  have hge := okB_ge s p len
  have hokr : HdrOkR R b len :=
    ⟨hS1 _ _ _ (by unfold makeCap; decide), by omega, fun _ d sr n hn => hS2 _ _ _ (by omega)⟩
  have hbudD : 3 * makeCost 4 + 3 * dCost ≤ b := by omega
  have henv : CallEnv R L s stk 40 := callEnv_mono' hW1 henvW
  have hWs : W ≤ s.sp.toNat := henvW.2.1.2.1
  refine runPre impl hap R hmk hmv hno b L c p len cp ret hret s hs henv hin hinv hokr hrecv (hS5 _) (by omega) Q
    (fun S' h => absurd h (by omega)) ?zero ?main
  case zero =>
    intro S' h0 _ h2 habi h1 h3 hfr
    obtain ⟨L', b', hext, hb', hinv', hMF', hLF'⟩ := hfr
    refine hOk S' habi ⟨h3, by rw [h1, h2]; rfl, by rw [h2, resV_zero h2]; rfl⟩
      ⟨L', b', hext, by omega, hinv', fun h => absurd h (by omega), hMF'.mono fun a n h => ?_, hLF'⟩
    simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    exact ⟨h.1, by omega⟩
  case main =>
  intro S L1 b1 hrH T' hTpc hTm hTsp hT28 hT29 hT18 hl0 hl1 hl2 hnz hr8 hr11 hr12 hr1 hr3 hr7
  refine d1 impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q S L1 b1 hrH T' hTpc hTm hTsp hT28 hT29 hT18
    hl0 hl1 hl2 hnz hr8 hr11 hr12 hr1 hr3 hr7 hbudD hokM hokB fun S2 L2 b2 hrel2 hpc2 => ?_
  refine d2 impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q hbudD S2 L2 b2 hrel2 hpc2 hokB hokM
    fun S3 L3 b3 hrel3 hpc3 => ?_
  refine d3 impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q hbudD S3 L3 b3 hrel3 hpc3 hokB hokM
    fun S4 L4 b4 hrel4 hx0 hx1 hpc4 => ?_
  refine c1 impl hap R hmk hokB b L c p len cp ret hret s henv hin Q W hW1 hWs (okB s p len) hge.1 hbB S4 L4 b4 hrel4
    hx0 hx1 hpc4 hOk fun hV T hTpc hTm hTsp hT28 hT29 hT18 h7 => ?_
  have hrelT := RelD.congr hrel4 hTm hTsp hT28 hT29 hT18
  have hkV : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.pc = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q := fun V Lk bk hrV hpcV =>
    cp1 impl hap R hmk hokB b L p len ret hret s W hW1 henvW Q hbB V Lk bk hrV hpcV hOk
      fun U Lk' bk' vp vn buf hj hpcU => cp2 impl hap R hmv hmz hokM' b L p len ret hret s W hW1 henvW Q hOk U Lk' bk'
        vp vn buf hj hpcU
  by_cases hv0 : opV s p len 0 = 1
  · exact c2m impl hap R stkM aboveM hM hBy hsv' b L c p len cp ret hret s Q W henvW hW hW1 hab hglob hgL hbB L4 b4 T
      hrelT hTpc h7 hv0 hV hkV
  · exact c2e impl hap R stkM aboveM hE hBy hsv' b L c p len cp ret hret s Q W henvW hW hW1 hab hglob hgL hbB L4 b4 T
      hrelT hTpc h7 hv0 hV hkV

end FvModexp.Arm64.Run
