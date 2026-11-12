import FvModexp.Proofs.Amd64.Int.IntASDefs
import FvModexp.Proofs.Common.Link
import FvModexp.Proofs.Amd64.Nat.Callees

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): calling `nat.add` / `nat.sub` / `nat.cmp` from `LibIntAS`

`hypSum`, `pairwise_ne`, `find_none_of`, `retAddr_restrict`: adapted from agent infra's `Amd64/Exp/CallW.lean`
(program `LibIntAS` instead of `LibExp`). `subCall` / `addCall`: adapted from infra's `Amd64/Exp/SubMod2NCall.lean`
(continuation form over the Nat-level post), with divmc's `NatSub.ensR` / `NatAdd.ensR` plugged in. `ra_of`: a return
address inside `(*Int).Add` / `(*Int).Sub`. `cmpSum`: asm's `CmpSum.cmp_summary` on `LibIntAS`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.IntAS

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem hypSum {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibIntAS.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibIntAS.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 args ∧ s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  have hS := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hlen (A64.codeIn_restrict_mono64 hap hns)
  rw [← LibIntAS.eq_only] at hS
  exact hS

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
theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem sub_names : ∀ x, NatSub.names.contains x = true → LibIntAS.names.contains x = true :=
  sub_of_all (by decide)

theorem add_names : ∀ x, NatAdd.names.contains x = true → LibIntAS.names.contains x = true :=
  sub_of_all (by decide)

set_option maxRecDepth 20000 in
/-- a return address inside `(*Int).Add` (`seg8`, `sub = false`) / `(*Int).Sub` (`seg7`) is a return address of
every callee program that does not contain the function -/
theorem ra_of {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (sub : Bool) (hn : ns.contains (fn sub) = false) (i : Nat) (hi : i < 0x1cc) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (entry sub + i) := by
  cases sub
  · have := retAddr_restrict hap (cs := Extracted.seg8) (ns := ns)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
      (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5e2620 + i < 2 ^ 47; omega)
    simpa only [Extracted.seg8, entry, Bool.false_eq_true, ↓reduceIte] using this
  · have := retAddr_restrict hap (cs := Extracted.seg7) (ns := ns)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
      (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5e2800 + i < 2 ^ 47; omega)
    simpa only [Extracted.seg7, entry, ↓reduceIte] using this

theorem cmpCodeIn (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.CmpAmd64.program (LibIntAS.program.link impl) := by
  rw [LibIntAS.eq_only]
  exact Callees.codeIn_single hap (seg := Extracted.seg15) rfl
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide)

/-- `nat.cmp` (asm's `CmpSum.cmp_summary`) on `LibIntAS` -/
theorem cmpSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibIntAS.program.link impl) 6184128 CmpSum.Pre CmpSum.Post :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn64 (cmpCodeIn impl hap) CmpSum.cmp_summary

set_option maxRecDepth 20000 in
/-- a call of `nat.sub` (divmc `NatSub.ensX`, exact write set) at its entry `6183136` with `RSP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem subCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat}
    {M : Memory} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatSub.names).link impl) ra)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (_bsp : sp' + 8 < 2 ^ 64) (bx39 : xl < 2 ^ 39)
    (hpc : S.rip = BitVec.ofNat 64 6183136) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = sp') (h14 : (S.regs 14).toNat = g)
    (hpre : NatSub.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 ra →
      s'.regs 4 = BitVec.ofNat 64 (sp' + 8) → s'.regs 5 = S.regs 5 → s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      s'.fsBase = S.fsBase → s'.df = S.df →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl - natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ xl → LiveExt R L L' → b - makeCost xl ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4288, sp' + 80)] ++ [(zp, zp + 8 * min xl zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * min xl zc)] → (xl ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 → p' < 2 ^ 64 →
      ReachesRet (LibIntAS.program.link impl) ret s' Q) :
    ReachesRet (LibIntAS.program.link impl) ret S Q := by
  have hS' := hypSum hap sub_names (by simp [numIntRegs])
    (NatSub.ensX impl hap R hmk hmv b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatSub.fn = 6183136 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hpre⟩
    fun s' hr ⟨⟨e1, e5, e3, e4⟩, ⟨hq, hr1, hr2⟩, hF, hLF⟩ hrg => ?_
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  · obtain ⟨hfs, hdf', p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, -, -⟩ := hq
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [win, hsp, h14] at hF hinv
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (by rw [hr, retAddrOf_eq, hrd]) ?_ e5 e3 e4 hfs hdf' hrg
      (by rw [← q0, bv_ofNat_toNat]) (by rw [← q1, bv_ofNat_toNat]) (by rw [← q2, bv_ofNat_toNat])
      hv hn hlc hln hLE hb hinv hlive hor (by simpa only [show 4288 + 80 = 4368 from rfl] using hF) hLF
      (fun h => ?_) (by rw [← q2]; exact hr2 bx39) (by rw [← q0]; exact BitVec.isLt _)
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (divmc `NatAdd.ensX`, exact write set) at its entry `6182240` with `RSP = sp'` -/
theorem addCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat}
    {M : Memory} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatAdd.names).link impl) ra)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (_bsp : sp' + 8 < 2 ^ 64) (bx39 : xl < 2 ^ 39) (by39 : yl < 2 ^ 39)
    (hpc : S.rip = BitVec.ofNat 64 6182240) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = sp') (h14 : (S.regs 14).toNat = g)
    (hpre : NatAdd.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 ra →
      s'.regs 4 = BitVec.ofNat 64 (sp' + 8) → s'.regs 5 = S.regs 5 → s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      s'.fsBase = S.fsBase → s'.df = S.df →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl + natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ max xl yl + 1 → LiveExt R L L' →
      b - makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4440, sp' + 80)] ++ [(zp, zp + 8 * min (max xl yl + 1) zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * min (max xl yl + 1) zc)] →
      ((if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 → p' < 2 ^ 64 →
      ReachesRet (LibIntAS.program.link impl) ret s' Q) :
    ReachesRet (LibIntAS.program.link impl) ret S Q := by
  have hS' := hypSum hap add_names (by simp [numIntRegs])
    (NatAdd.ensX impl hap R hmk hmv b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatAdd.fn = 6182240 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hpre⟩
    fun s' hr ⟨⟨e1, e5, e3, e4⟩, ⟨hq, hr1, hr2⟩, hF, hLF⟩ hrg => ?_
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  · obtain ⟨hfs, hdf', p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, -, -⟩ := hq
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [win, hsp, h14] at hF hinv
    simp only [NatAdd.mx, NatAdd.need, tN bxl, tN byl] at hln hb hr1 hr2
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (by rw [hr, retAddrOf_eq, hrd]) ?_ e5 e3 e4 hfs hdf' hrg
      (by rw [← q0, bv_ofNat_toNat]) (by rw [← q1, bv_ofNat_toNat]) (by rw [← q2, bv_ofNat_toNat])
      hv hn hlc hln hLE hb hinv hlive hor hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 (by omega)) (by rw [← q0]; exact BitVec.isLt _)
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

end FvModexp.Amd64.IntAS
