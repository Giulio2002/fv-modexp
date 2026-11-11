import FvModexp.Proofs.Arm64.Int.IntBytesLoop

/-!
# `(*Int).Bytes` (arm64): `ens` (= `RunIface.BytesSpec` at `stk = 4160`, `above = 16`) and `sum`

Prologue, `make([]byte, 8·len)` (`makeslice(uint8, n, n)`), then the loops (`IntBytesLoop.outerLoop`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.IntBytes

set_option maxRecDepth 20000 in
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn) [x]
      (Pre R b L x) (Post R b L x) := by
  intro ret hret s hs ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hgl, hB, hinv,
    hints, _⟩, hlen⟩
  obtain ⟨⟨hneg, hx8, hx48, hxacc, hxheld, hlive, hlc, hnorm, hxarr⟩, hxw, harw, hxg, harg⟩ :=
    hints x.toNat (List.mem_singleton_self _)
  have hmk' := MakesliceLiveContract.of_codeIn (codeIn_ofImpl_restrict_of_apart hap [fn]) hmk
  have hok := hsv.1 uint8T (8 * lenW s.mem x.toNat) (8 * lenW s.mem x.toNat) (by unfold IntLenLe maxW lenW at *; omega)
  have hLs0 := hLs
  janus_intro hs
  simp only [LiveSep, win] at hLs
  by_cases hal0 : s.mem.readLE (x.toNat + 16) 8 = 0
  · janus_run calls [hmk']
    all_goals trace_state
    all_goals sorry
  · janus_run until [hOuter] calls [hmk'.pos]
    all_goals trace_state
    all_goals sorry

end FvModexp.Arm64.IntBytes
