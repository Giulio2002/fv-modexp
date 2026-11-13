import FvModexp.Proofs.Amd64.NatQ.DivLargeDB

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeDBR.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `n < divRecursiveThreshold` → `q.divBasic(stk, u, v)` (natdiv.go:623-627), `joinQ` → `joinD`

`Mem.thr`: the threshold global `divRecursiveThreshold` (`= 40`, at `gA = 0xb4ae88`) is unchanged since the entry.
`ra_dl`: return addresses inside `nat.divLarge` (`seg27`). `db2`: at `divBasic`'s entry, the call (`DivBasic.ensL`).
`db`: from `joinQ` (`q` slots stored at `+0x58f`, `CMPQ divRecursiveThreshold, R11; JG +0x649`, args at `+0x649`) to
the call. Port of `Arm64/Nat/DivLargeDB.lean` / `DivLargeDBR.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- the threshold global keeps its value (pure) -/
theorem Mem.thr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hM : Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk M) :
    M.readLE 11841160 8 = 40 ∧ M.accessible 11841160 8 false = true ∧
      (11841160 + 32 ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ 11841160) := by
  have hpre := hE.pre
  have eg : RunIface.gA = 11841160 := rfl
  obtain ⟨-, -, -, h40, -, -, -, hacc, hrt, hw, -⟩ := hpre.gl
  have hga := hpre.ga
  replace h40 : s.mem.readLE 11841160 8 = 40 := h40
  rw [eg] at hacc hrt hw hga
  obtain ⟨hz, hu, hs, hf⟩ := hga
  simp only [win, outside_cons, outside_nil, and_true] at hw
  refine ⟨?_, by rw [hM.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega), hw⟩
  rw [hM.fr.readLE _ _ ?_]; exact h40
  have hlc := hpre.sti.1.2.2.2.2.2.1
  simp only [outside_append]
  refine ⟨⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩, ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true]; omega
  · refine outside_wsL ?_ (fun h => by have := hz h; unfold Apart at this; omega)
      (fun h => by have := hu h; unfold Apart at this; omega)
    rcases hE.scr.loc with ⟨-, h1, h2⟩ | ⟨hin, -⟩
    · unfold Apart at hf; omega
    · have := outside_of_inRanges hrt hin; omega
  · unfold Apart at hs hf
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega

-- `pairwise_ne`, `find_none_of`, `retAddr_restrict`: adapted from Amd64/Int/IntASCallH.lean (agent divmc; itself from infra's
-- Amd64/Exp/CallW.lean), copied to keep the divLarge chain free of the `(*Int).Add/Sub` modules

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hR _ _ (hp.1 a ha')
      · exact pairwise_ne hR hp.2 ha' hb' hne

theorem find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact find_none_of h x hx'

/-- A return address inside the code of a segment `cs` of `P` whose name is not in `ns` is a `RetAddr` of the
restricted program of `ns` (amd64). -/
theorem retAddr_restrict {P : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
    {ns : List String} {cs : Amd64.Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat)
    (hi : i < cs.bytes.length) (hu : cs.base + i < 2 ^ 47) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + i) := by
  refine ⟨hu, fun seg hseg => ?_, fun st hst => ?_⟩
  · have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have hne : seg ≠ cs := by
      rintro rfl
      rcases List.mem_append.1 hseg with h | h
      · have := (List.mem_filter.1 h).2
        rw [hn] at this; exact absurd this (by decide)
      · have := hap.1
        rw [List.pairwise_append] at this
        have := this.2.2 seg hcs seg h
        unfold Amd64.Segment.Apart at this
        omega
    have := pairwise_ne (fun a b h => by unfold Amd64.Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Amd64.Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Amd64.Program.stubAt at h1
    have := find_none_of h1 st hst
    simp at this
    exact this

set_option maxRecDepth 20000 in
/-- a return address inside `nat.divLarge` (`seg27`, base `0x5ee920`) is a return address of every callee program
that does not contain `nat.divLarge` -/
theorem ra_dl {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x813) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn + i) := by
  have := retAddr_restrict hap (cs := Extracted.seg27) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg27.name = fn from rfl]; exact hn) i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5ee920 + i < 2 ^ 47; omega)
  rw [show Extracted.seg27.base = 0x5ee920 from rfl] at this
  rw [show segAddr Extracted.program fn = 0x5ee920 by decide]; exact this

theorem tN64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `divBasic`'s entry: the call, then `AtD` -/
theorem db2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (dc : Nat → Nat → Nat) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (X : State)
    (hpc : X.rip = BitVec.ofNat 64 (segAddr Extracted.program DivBasic.fn))
    (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 312)
    (hrd : X.mem.readLE (X.regs 4).toNat 8 = joinD) (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14)
    (hfs : X.fsBase = s.fsBase) (hx15 : X.xmm 15 = 0#128) (hdf : X.df = false)
    (hr0 : X.regs 0 = BitVec.ofNat 64 qp) (hr3 : X.regs 3 = BitVec.ofNat 64 (il - vl + 1))
    (hr7 : X.regs 7 = BitVec.ofNat 64 st) (hr6 : X.regs 6 = BitVec.ofNat 64 P)
    (hr8 : X.regs 8 = BitVec.ofNat 64 (il + 1)) (hr9 : X.regs 9 = BitVec.ofNat 64 C)
    (hF : MemFrame S.mem X.mem (callWs s))
    (hq0 : X.mem.readLE ((s.regs 4).toNat - 64) 8 = qp) (hq1 : X.mem.readLE ((s.regs 4).toNat - 56) 8 = il - vl + 1)
    (hq2 : X.mem.readLE ((s.regs 4).toNat - 48) 8 = qc)
    (hvS : X.mem.readLE ((s.regs 4).toNat - 304) 8 = t) (hlS : X.mem.readLE ((s.regs 4).toNat - 296) 8 = vl)
    (hreg : X.mem.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) X Q := by
  have hl := hE.lay
  have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2; have hsp0 := hl.sp0
  have hcap := hS.ua.cap; have hc40 := hS.ua.c40; have hqcap := hS.qa.cap; have hq40 := hS.qa.c40
  have e0 : (BitVec.ofNat 64 qp).toNat = qp := tN64 (by have := hS.qa.p48; omega)
  have e1 : (BitVec.ofNat 64 (il - vl + 1)).toNat = il - vl + 1 := tN64 (by omega)
  have e2 : (BitVec.ofNat 64 qc).toNat = qc := tN64 (by omega)
  have e3 : (BitVec.ofNat 64 st).toNat = st := tN64 (by have := hl.st48; omega)
  have e4 : (BitVec.ofNat 64 P).toNat = P := tN64 (by have := hS.ua.p48; omega)
  have e5 : (BitVec.ofNat 64 (il + 1)).toNat = il + 1 := tN64 (by omega)
  have e6 : (BitVec.ofNat 64 C).toNat = C := tN64 (by omega)
  have hcost : stkRes H - potK * c1 ≤ bq := by
    have := bud_div hE hS.bud3; omega
  have hpre := db_pre hE hS X hspn h14 hfs hF hreg hvS hlS hcost
  have hc : CodeIn64 ((Extracted.program.onlySegments DivBasic.names).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hsum := Ensures.toSummaryRegs7 (fun a0 a1 a2 a3 a4 a5 a6 =>
    DivBasic.ensL impl hap R hgr hmc hwb H bq Lq a0 a1 a2 a3 a4 a5 a6 t vl) (A64.noExit_restrict64 hap DivBasic.names) hc
  refine ReachesRet.call_regions hsum hpc ⟨?_, hx15, hdf, ?_⟩ fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_
  · simp only [regSP]; rw [hrd]
    exact ra_dl (i := 0x676) hap (by decide) (by decide)
  · rw [hr0, hr3, hr7, hr6, hr8, hr9, e0, e1, e3, e4, e5, e6]; exact hpre
  rw [hr0, hr3, hr7, hr6, hr8, e0, e1, e3, e4, e5] at hq
  obtain ⟨qfs, qdf, hqv, hrv, L', b', hx, hb, hinv, hSB, hMF, hLF⟩ := hq
  have hqn : DivBasic.qn (il - vl + 1) (il + 1) vl = il - vl + 1 := by
    simp only [DivBasic.qn]; rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]; omega
  have hqv' := hqv (by omega)
  rw [hqn] at hqv'
  simp only [DivBasic.ws, hqn] at hMF hLF
  rw [h14] at hinv
  have hsp' : T.regs 4 = s.regs 4 - 304#64 := by
    rw [f4]; bv_omega
  exact k _ _ _ _ T (dbPost hE hS hspn hF hq0 hq1 hq2 hreg (by rw [hT, retAddrOf, hrd]) hsp' (by rw [f5, h5])
    (by rw [f14, h14]) (by rw [qfs, hfs]) (by rw [f15, hx15]) (by rw [qdf, hdf]) hrg hqv' hrv hx hb hinv hSB
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hMF) hLF)

end FvModexp.Amd64.Q.DivLarge
