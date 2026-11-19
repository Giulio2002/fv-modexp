import FvModexp.Proofs.Amd64.Int.IntBytesLoop
import FvModexp.Proofs.Amd64.Int.IntBytesMid
import FvModexp.Proofs.Amd64.Top.RunIfaceMono
import FvModexp.Proofs.Amd64.SetRetLemmas

/-!
# `(*Int).Bytes` (amd64): `ens` (= `RunIface.BytesSpec` at `stk = 4160`, `above = 16`) and `sum`

Prologue, `make([]byte, 8·len)` (`makeslice(uint8, n, n)`), then the loops (`IntBytesLoop.outerLoop`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface

namespace FvModexp.Amd64.IntBytes

theorem intbytes_setRet_p (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < s.mem.readLE (x.toNat + 24) 8)
    (hp : FvModexp.Amd64.IntBytes.Pre R b L x s) :
    FvModexp.Amd64.IntBytes.Pre R b L x (s.setRet ret) := by
  simp only [FvModexp.Amd64.IntBytes.Pre, FvModexp.Amd64.RunIface.IntPre, List.forall_mem_cons, List.forall_mem_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, true_and, forall_eq, List.mem_singleton, forall_eq_or_imp, false_implies, implies_true, forall_const, List.Pairwise.nil] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.IntBytes.Pre, FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.IntOK, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, false_implies, true_implies]

theorem intbytes_setRet_n (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ¬ 0 < s.mem.readLE (x.toNat + 24) 8)
    (hp : FvModexp.Amd64.IntBytes.Pre R b L x s) :
    FvModexp.Amd64.IntBytes.Pre R b L x (s.setRet ret) := by
  simp only [FvModexp.Amd64.IntBytes.Pre, FvModexp.Amd64.RunIface.IntPre, List.forall_mem_cons, List.forall_mem_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, true_and, forall_eq, List.mem_singleton, forall_eq_or_imp, false_implies, implies_true, forall_const, List.Pairwise.nil] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.IntBytes.Pre, FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.IntOK, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, false_implies, true_implies]

theorem intbytes_setRet (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64)  (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) 
    (hp : FvModexp.Amd64.IntBytes.Pre R b L x s) :
    FvModexp.Amd64.IntBytes.Pre R b L x (s.setRet ret) := by
  by_cases hg0 : 0 < s.mem.readLE (x.toNat + 24) 8
  · exact intbytes_setRet_p R b L x  s ret hs hret  hg0 hp
  · exact intbytes_setRet_n R b L x  s ret hs hret  hg0 hp

/-- `Pre` survives writing the return address (the `hinv` of `ens`): the list quantifier of `IntPre` is expanded and the guard `0 < cap x` is
case-split (`intbytes_setRet_<x>`). -/
theorem intbytes_inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (p : Janus.Amd64.Program) (entry : Nat) (args : List W64) :
    Ensures.SetRetInv p entry args (fun s => Pre R b L x s) :=
  fun s ret hs hret hp => intbytes_setRet R b L x s ret hs hret hp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem ens (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn) [x]
      (Pre R b L x) (Post R b L x) := by
  refine Ensures.of_old (intbytes_inv R b L x _ _ _) ?_
  intro ret hret s hs ⟨⟨⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro⟩, hsv, hgl, hB, hinv,
    hints, _⟩, hlen⟩
  obtain ⟨⟨hneg, hx8, hx48, hxacc, hxheld, hlive, hlc, hnorm, hxarr⟩, hxw, harw, hxg, harg, hxt, hart⟩ :=
    hints x.toNat (List.mem_singleton_self _)
  have hmk' := MakesliceLiveContract64.of_codeIn (codeIn_ofImpl_restrict_of_apart64 hap [fn]) hmk
  have hmz' := MakesliceZeroLive64.of_codeIn (codeIn_ofImpl_restrict_of_apart64 hap [fn]) hmz
  have hLs0 := hLs
  have hgl' := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl' hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  janus64_intro hs
  simp only [LiveSep, win] at hLs
  unfold IntLenLe maxW at hlen
  unfold BytesBudget lenW at hB
  simp only [Outside, and_true] at hxw
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [uint8T, 8 * s.mem.readLE (x.toNat + 16) 8, 8 * s.mem.readLE (x.toNat + 16) 8] :=
    hsv.1 _ _ _ (by omega)
  rw [h_u] at hokb
  have hsh : BitVec.ofNat 64 (s.mem.readLE (x.toNat + 16) 8) <<< 3 = BitVec.ofNat 64 (8 * s.mem.readLE (x.toNat + 16) 8) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft]; simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  obtain ⟨hU2, hU3, hU1⟩ := u8B hd
  have hut : Apart 7231264 16 ((s.regs 4).toNat - 4160) (4160 + 16) :=
    apart_of_data (x := 7231264) (l := 16) hd 0 (by decide) (by decide) hw
  unfold Apart at hut
  have hBS : blockSize (8 * s.mem.readLE (x.toNat + 16) 8) true ≤ b :=
    Nat.le_trans (blockSize_le_allocCost _ true) hB
  have hIp := toInt_small (BitVec.ofNat 64 (8 * s.mem.readLE (x.toNat + 16) 8)) (by simp; omega)
  have hLSc : ∀ r ∈ L, (r.fst + (r.snd - r.fst) ≤ (s.regs 4).toNat - 48 - 4096 ∨ (s.regs 4).toNat - 48 ≤ r.fst) ∧
      (r.fst + (r.snd - r.fst) ≤ (s.regs 4).toNat - 48 + 8 ∨ (s.regs 4).toNat - 48 + 8 + 24 ≤ r.fst) ∧
      (r.fst + (r.snd - r.fst) ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 48 + 8 ≤ r.fst) := by
    intro r hr; have := hLs r hr
    simp only [Outside, and_true] at this; omega
  clear hints hLs hgl
  have hxw' : x.toNat + 32 ≤ (s.regs 4).toNat - 4160 ∨ (s.regs 4).toNat + 16 ≤ x.toNat := by omega
  by_cases hal0 : s.mem.readLE (x.toNat + 16) 8 = 0
  · have hmzP := hmz' L b
    simp only [hal0, Nat.mul_zero] at hokb
    janus64_run [hsh, hU2, hU3, hIp, BitVec.msb_eq_decide] until [hOuter] calls [hmzP]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hinv'
    have hxk := read_kept (hbuf := by intro a k h1 h2; janus64_simp) hb' hxheld hxw' hLF hMF
    have hx16 : m.readLE (x.toNat + 16) 8 = 0 := by rw [hxk _ _ (by omega) (by omega)]; exact hal0
    janus64_run [hx16, hal0, BitVec.msb_eq_decide]
    refine post_zero hLs0 hb' ?_ hLF hMF hinv' hal0 (by janus64_simp) (by janus64_simp) rfl (by janus64_simp) (by janus64_simp)
    simp only [win]; janus_frame
  · have hmkP := hmk'.pos L b
    janus64_run [hsh, hU2, hU3, hIp, BitVec.msb_eq_decide] until [hOuter] calls [hmkP]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv'
    have hxk := read_kept (hbuf := by intro a k h1 h2; janus64_simp) hb' hxheld hxw' hLF hMF
    have hx8' : m.readLE (x.toNat + 8) 8 = s.mem.readLE (x.toNat + 8) 8 := hxk _ _ (by omega) (by omega)
    have hx16' : m.readLE (x.toNat + 16) 8 = s.mem.readLE (x.toNat + 16) 8 := hxk _ _ (by omega) (by omega)
    have hc0 : 0 < s.mem.readLE (x.toNat + 24) 8 := by omega
    obtain ⟨-, habsH, habsA, habs48⟩ := hlive hc0
    have habW := harw hc0
    simp only [Outside, and_true] at habW
    have hI := inv_of_alloc (x := x) (ret := ret) (N := 8 * s.mem.readLE (x.toNat + 16) 8) hLs0 hout hb'
      (habsH.sub (Nat.le_refl _) (by omega)) (by omega) (by janus64_simp) (by janus64_simp)
      (by intro a k h1 h2; janus64_simp) (by simp only [win]; janus_frame) hLF hMF hAp hIn (by omega) hacc hinv' hsz
      (by unfold BytesBudget; rw [show 8 * s.mem.readLE (x.toNat + 16) 8 / 8 = s.mem.readLE (x.toNat + 16) 8 by omega];
          exact blockSize_le_allocCost _ true) (by omega)
    refine outerLoop impl R b L x ret hret s ptr.toNat _ _ _ _ (by omega) rfl rfl
      (Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ habsA (Nat.le_refl _) (by omega)))
      (by omega) ⟨hb', ha, hal⟩ hw (s.mem.readLE (x.toNat + 16) 8) _ m 0 (by omega) (by simpa using hI)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus64_simp) (by janus64_simp) rfl
    all_goals janus64_simp [hx8', hx16']
    all_goals first
      | rw [show 8 * s.mem.readLE (x.toNat + 16) 8 / 8 = s.mem.readLE (x.toNat + 16) 8 by omega]
      | rw [Nat.sub_zero]
      | (apply BitVec.eq_of_toNat_eq; simp; omega)

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ [fn]` (amd64). -/
def sum (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (ms : List String)
    (hsub : ∀ y, [fn].contains y = true → ms.contains y = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmz b L x) (FvModexp.A64.noExit_restrict64 hap [fn])
    (by simp [numIntRegs]) (FvModexp.A64.codeIn_restrict_mono64 hap hsub)

/-- **`(*Int).Bytes` meets `RunIface.BytesSpec`** (amd64) at its own window (`stk = 4160`, `above = 16`). -/
theorem bytesSpec (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R) :
    BytesSpec impl R 4160 16 :=
  fun b L x => ens impl hap R hmk hmz b L x

/-- ... and at every larger window. -/
theorem bytesSpec_at (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (stk above : Nat) (hk : 4160 ≤ stk) (ha : 16 ≤ above) : BytesSpec impl R stk above :=
  (bytesSpec impl hap R hmk hmz).mono hk ha

end FvModexp.Amd64.IntBytes
