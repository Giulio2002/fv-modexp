import FvModexp.Proofs.Arm64.Int.IntBytesLoop
import FvModexp.Proofs.Arm64.Int.IntBytesMid
import FvModexp.Proofs.Arm64.Top.RunIfaceMono
import FvModexp.Proofs.Common.DivmcLsl

/-!
# `(*Int).Bytes` (arm64): `ens` (= `RunIface.BytesSpec` at `stk = 4160`, `above = 16`) and `sum`

Prologue, `make([]byte, 8·len)` (`makeslice(uint8, n, n)`), then the loops (`IntBytesLoop.outerLoop`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.IntBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn) [x]
      (Pre R b L x) (Post R b L x) := by
  janus_ensures_old [FvModexp.Arm64.IntBytes.Pre, FvModexp.Arm64.RunIface.IntPre, FvModexp.Arm64.RunIface.lenW, FvModexp.Arm64.RunIface.IntLenLe, FvModexp.Arm64.RunIface.maxW, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.win, FvModexp.Arm64.RunIface.IntOK, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.gA, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.NatNorm]
  intro ret hret s hs ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hgl, hB, hinv,
    hints, _⟩, hlen⟩
  obtain ⟨⟨hneg, hx8, hx48, hxacc, hxheld, hlive, hlc, hnorm, hxarr⟩, hxw, harw, hxg, harg⟩ :=
    hints x.toNat (List.mem_singleton_self _)
  have hmk' := MakesliceLiveContract.of_codeIn (codeIn_ofImpl_restrict_of_apart hap [fn]) hmk
  have hmz' := MakesliceZeroLive.of_codeIn (codeIn_ofImpl_restrict_of_apart hap [fn]) hmz
  have hLs0 := hLs
  janus_intro hs
  simp only [LiveSep, win] at hLs
  unfold IntLenLe maxW at hlen
  unfold BytesBudget lenW at hB
  have hsh := lsl3_ofNat (s.mem.readLE (x.toNat + 16) 8) (by omega)
  simp only [Outside, and_true] at hxw
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [uint8T, 8 * s.mem.readLE (x.toNat + 16) 8, 8 * s.mem.readLE (x.toNat + 16) 8] :=
    hsv.1 _ _ _ (by omega)
  rw [h_u] at hokb
  have hU2 : s.mem.readLE 2639168 8 = 1 := by
    janus_data hd; rw [h_rodata _ _ (by decide)]; decide
  have hU3 : s.mem.readLE 2639176 8 = 0 := by
    janus_data hd; rw [h_rodata _ _ (by decide)]; decide
  have hut : Apart 2639168 16 (s.sp.toNat - 4160) (4160 + 16) :=
    apart_of_data (x := 2639168) (l := 16) hd 0 (by decide) (by decide) hw
  unfold Apart at hut
  have hU1 : s.mem.accessible 2639168 16 false = true := by
    janus_data hd; exact Memory.accessible_mono _ h_data0 (by omega) (by omega)
  have hBS : blockSize (8 * s.mem.readLE (x.toNat + 16) 8) true ≤ b :=
    Nat.le_trans (blockSize_le_allocCost _ true) hB
  have hIp := toInt_small (BitVec.ofNat 64 (8 * s.mem.readLE (x.toNat + 16) 8)) (by simp; omega)
  have hLSc : ∀ r ∈ L, (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 64 - 4096 ∨ s.sp.toNat - 64 - 8 ≤ r.fst) ∧
      (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 64 + 8 ∨ s.sp.toNat - 64 + 8 + 24 ≤ r.fst) := by
    intro r hr; have := hLs r hr
    simp only [Outside, and_true] at this; omega
  clear hints hLs hgl
  have hxw' : x.toNat + 32 ≤ s.sp.toNat - 4160 ∨ s.sp.toNat + 16 ≤ x.toNat := by omega
  by_cases hal0 : s.mem.readLE (x.toNat + 16) 8 = 0
  · have hmzP := hmz' L b
    janus_run [hsh, hU2, hU3, hIp] until [hOuter] calls [hmzP]
    rename_i ptr _ _ _ m _ _ hLF hMF hinv'
    have hxk := read_kept (hbuf := by intro a k h1 h2; janus_simp) hb' hxheld hxw' hLF hMF
    have hx16 : m.readLE (x.toNat + 16) 8 = 0 := by rw [hxk _ _ (by omega) (by omega)]; exact hal0
    janus_run [hx16, hal0]
    refine post_zero hLs0 hb' ?_ hLF hMF hinv' hal0 rfl (by janus_simp) (by janus_simp)
    simp only [winA]; janus_frame
  · have hmkP := hmk'.pos L b
    janus_run [hsh, hU2, hU3, hIp] until [hOuter] calls [hmkP]
    rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv'
    have hxk := read_kept (hbuf := by intro a k h1 h2; janus_simp) hb' hxheld hxw' hLF hMF
    have hx8' : m.readLE (x.toNat + 8) 8 = s.mem.readLE (x.toNat + 8) 8 := hxk _ _ (by omega) (by omega)
    have hx16' : m.readLE (x.toNat + 16) 8 = s.mem.readLE (x.toNat + 16) 8 := hxk _ _ (by omega) (by omega)
    have hc0 : 0 < s.mem.readLE (x.toNat + 24) 8 := by omega
    obtain ⟨-, habsH, habsA, habs48⟩ := hlive hc0
    have habW := harw hc0
    simp only [Outside, and_true] at habW
    have hI := inv_of_alloc (x := x) (ret := ret) (N := 8 * s.mem.readLE (x.toNat + 16) 8) hLs0 hout hb'
      (habsH.sub (Nat.le_refl _) (by omega)) (by omega) (by janus_simp) (by janus_simp)
      (by intro a k h1 h2; janus_simp) (by simp only [winA]; janus_frame) hLF hMF hAp hIn (by omega) hacc hinv' hsz
      (by unfold BytesBudget; rw [show 8 * s.mem.readLE (x.toNat + 16) 8 / 8 = s.mem.readLE (x.toNat + 16) 8 by omega];
          exact blockSize_le_allocCost _ true) (by omega)
    refine outerLoop impl R b L x ret hret s ptr.toNat _ _ _ _ (by omega) rfl rfl
      (Memory.accessible_read_of_write _ (Memory.accessible_mono _ habsA (Nat.le_refl _) (by omega))) (by omega)
      ⟨hb', ha, hal⟩ hw (s.mem.readLE (x.toNat + 16) 8) _ m 0 (by omega) (by simpa using hI) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals janus_simp [hx8', hx16']
    all_goals first
      | rw [show 8 * s.mem.readLE (x.toNat + 16) 8 / 8 = s.mem.readLE (x.toNat + 16) 8 by omega]
      | rw [Nat.sub_zero]

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ [fn]`. -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (ms : List String)
    (hsub : ∀ y, [fn].contains y = true → ms.contains y = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmz b L x) (noExit_restrict hap [fn]) (codeIn_restrict_mono hap hsub)

/-- **`(*Int).Bytes` meets `RunIface.BytesSpec`** at its own window (`stk = 4160`, `above = 16`). -/
theorem bytesSpec (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R) :
    BytesSpec impl R 4160 16 :=
  fun b L x => ens impl hap R hmk hmz b L x

/-- ... and at every larger window (`Run` calls `Mod`, `exp`, `Bytes` with one window). -/
theorem bytesSpec_at (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (stk above : Nat) (hk : 4160 ≤ stk) (ha : 16 ≤ above) : BytesSpec impl R stk above :=
  (bytesSpec impl hap R hmk hmz).mono hk ha

end FvModexp.Arm64.IntBytes
