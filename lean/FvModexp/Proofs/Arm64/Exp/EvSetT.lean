import FvModexp.Proofs.Arm64.Exp.EvSetR
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the tail of `z = z.set(z2)` — `setJ` → `mvJ` (agent infra)

nat.go:93-94 (`copy(z, z2)` of the inlined `set`): at `setJ` (`JS`) `z`'s array `(pZ, cZ)` is chosen (entry `z`
reused, or a fresh `makeslice`), `DZ` = `LZ` without the value. `runJ` spills `z` (`272/168/176`; `JO` = the facts
after these stores) and either skips the copy (same pointer, `BEQ`) or calls `memmove(pZ, pw, 8·lw)` (`lw = 0`:
`MemmoveZeroLive`, the local PR #2 copy). `setT`: `JS → J9`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- `z`'s array as a destination of length `l` (`LZ` without the value) -/
@[reducible] def DZ (R : RtInv) (L : List (Nat × Nat)) (st zp zc : Nat) (M : Memory) (L1 : List (Nat × Nat))
    (p l c : Nat) : Prop :=
  c < 2 ^ 40 ∧ NatLive M R L1 p c ∧ (0 < c → ZOK R L st zp zc M L1 p c) ∧ l ≤ c

/-- `DZ` through a step keeping accessibility and the stack header (live set extended) -/
theorem DZ.frm {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    (hx : LiveExt R L1 L2) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) (hhd : HdrEq st M M')
    {p l c : Nat} (hq : DZ R L st zp zc M L1 p l c) : DZ R L st zp zc M' L2 p l c := by
  obtain ⟨c40, hlv, hz, hlc⟩ := hq
  refine ⟨c40, fun hc => ?_, fun c0 => ?_, hlc⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hlv hc
    exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩
  · rcases hz c0 with e | ⟨hin, hap, hob⟩
    · exact Or.inl e
    · exact Or.inr ⟨hin, hap, hob.mono hx (by rw [hhd.2.1]; exact Nat.le_refl _) (Or.inl ⟨hhd.1, hhd.2.2⟩)⟩

/-- the join point `setJ` (`z`'s array chosen; `X0..X5` as `runJ` needs them) -/
structure JS (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  pc : S.pc = BitVec.ofNat 64 setJ
  r0 : S.regs 0 = BitVec.ofNat 64 pw
  r1 : S.regs 1 = BitVec.ofNat 64 lw
  r2 : S.regs 2 = BitVec.ofNat 64 cw
  r3 : S.regs 3 = BitVec.ofNat 64 cZ
  r4 : S.regs 4 = BitVec.ofNat 64 lw
  r5 : S.regs 5 = BitVec.ofNat 64 pZ
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s264 : S.mem.readLE (sp + 264) 8 = pz
  s152 : S.mem.readLE (sp + 152) 8 = lz
  s160 : S.mem.readLE (sp + 160) 8 = cz
  s256 : S.mem.readLE (sp + 256) 8 = pw
  s136 : S.mem.readLE (sp + 136) 8 = lw
  s144 : S.mem.readLE (sp + 144) 8 = cw
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  pz64 : pz < 2 ^ 64
  z1e : EL R L pz cz
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  z2 : LN R L s.mem st S.mem L1 pw lw cw
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pw64 : pw < 2 ^ 64
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)
  dz : DZ R L st zp zc S.mem L1 pZ lw cZ
  pZ64 : pZ < 2 ^ 64
  Za1 : 0 < cZ → Apart pZ (8 * cZ) p1 (8 * c1)
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz1 : 0 < cZ → 0 < cz → Apart pZ (8 * cZ) pz (8 * cz)
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)
  lwm : lw ≤ ml

/-- the facts after `runJ`'s spills of `z` (no pc / registers; `z` not yet copied) -/
structure JO (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat) : Prop where
  jx : JX R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s S L1 b1 (ℓ4 s st mp ml l1 l2) rk
  s288 : S.mem.readLE (sp + 288) 8 = p1
  s208 : S.mem.readLE (sp + 208) 8 = l1
  s216 : S.mem.readLE (sp + 216) 8 = c1
  s280 : S.mem.readLE (sp + 280) 8 = q
  s192 : S.mem.readLE (sp + 192) 8 = l2
  s200 : S.mem.readLE (sp + 200) 8 = a2 ml (nE s mp ml)
  s264 : S.mem.readLE (sp + 264) 8 = pz
  s152 : S.mem.readLE (sp + 152) 8 = lz
  s160 : S.mem.readLE (sp + 160) 8 = cz
  s256 : S.mem.readLE (sp + 256) 8 = pw
  s136 : S.mem.readLE (sp + 136) 8 = lw
  s144 : S.mem.readLE (sp + 144) 8 = cw
  s272 : S.mem.readLE (sp + 272) 8 = pZ
  s168 : S.mem.readLE (sp + 168) 8 = lw
  s176 : S.mem.readLE (sp + 176) 8 = cZ
  m1 : LN R L s.mem st S.mem L1 p1 l1 c1 (2 ^ nE s mp ml)
  c1p : 0 < c1
  m2 : LN R L s.mem st S.mem L1 q l2 (a2 ml (nE s mp ml)) (natVal s.mem mp ml / 2 ^ nE s mp ml)
  ap : Apart q (8 * a2 ml (nE s mp ml)) p1 (8 * c1)
  z1 : LN R L s.mem st S.mem L1 pz lz cz (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ nE s mp ml)
  pz64 : pz < 2 ^ 64
  z1e : EL R L pz cz
  za1 : 0 < cz → Apart pz (8 * cz) p1 (8 * c1)
  za2 : 0 < cz → Apart pz (8 * cz) q (8 * a2 ml (nE s mp ml))
  z2 : LN R L s.mem st S.mem L1 pw lw cw
    (natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
  pw64 : pw < 2 ^ 64
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)
  dz : DZ R L st zp zc S.mem L1 pZ lw cZ
  pZ64 : pZ < 2 ^ 64
  Za1 : 0 < cZ → Apart pZ (8 * cZ) p1 (8 * c1)
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz1 : 0 < cZ → 0 < cz → Apart pZ (8 * cZ) pz (8 * cz)
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

/-- `JO` + pc / registers + `z`'s value ⇒ `J9` -/
theorem JO.toJ9 {rk : Nat} {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : JO R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ)
    (hpc : S.pc = BitVec.ofNat 64 mvJ) (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h2 : S.regs 2 = BitVec.ofNat 64 cw)
    (h4 : S.regs 4 = BitVec.ofNat 64 lw) (hv : natVal S.mem pZ lw = natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
    (hn : NatNorm S.mem pZ lw) :
    J9 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ :=
  ⟨h.jx, hpc, h0, h2, h4, h.s288, h.s208, h.s216, h.s280, h.s192, h.s200, h.s264, h.s152, h.s160, h.s256, h.s136,
    h.s144, h.s272, h.s168, h.s176, h.m1, h.c1p, h.m2, h.ap, h.z1, h.pz64, h.z1e, h.za1, h.za2, h.z2, h.pw64, h.wa1, h.wa2,
    h.wz, ⟨h.dz.1, h.dz.2.1, h.dz.2.2.1, h.dz.2.2.2, hv, hn⟩, h.pZ64, h.Za1, h.Za2, h.Zz1, h.Zz2⟩

/-- an apartness from `[p, p + 8c)` gives one from a destination inside it (or an empty one at `0`) -/
theorem ap_dst {p c d n a k : Nat} (hd : (d = 0 ∧ n = 0) ∨ (d = p ∧ n ≤ 8 * c ∧ 0 < c))
    (h : 0 < c → Apart a k p (8 * c)) : Apart a k d n := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hn, hc⟩
  · unfold Apart; omega
  · have := h hc; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- **`JO` through `memmove(d, ·, n)`** with `[d, d + n)` empty at `0` or inside `z`'s array: every local and slot
kept, `WC` kept; the state `S'` has the memory after the call and `S`'s `SP` / `X18` / `X28` / `X29` -/
theorem JO.mv (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {rk : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : JO R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ)
    {d n : Nat} (hd : (d = 0 ∧ n = 0) ∨ (d = pZ ∧ n ≤ 8 * cZ ∧ 0 < cZ)) {m : Memory}
    (hF : MemFrame S.mem m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(d, d + n)]))
    (hLF : LiveFrame S.mem m L1 [(d, d + n)]) (hrg : m.regions = S.mem.regions)
    (hinv : R.inv b1 L1 g (view R.rt L1 m)) (S' : State) (esp : S'.sp = S.sp) (e28 : S'.regs 28 = S.regs 28)
    (e29 : S'.regs 29 = S.regs 29) (e18 : S'.regs 18 = S.regs 18) (hm : S'.mem = m) :
    JO R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s rk S' L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 448) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := h.jx.wc
  -- the destination is apart from the window, the header; inside what the function may write
  have hzap : 0 < cZ → Held R L1 pZ (8 * cZ) ∧ Apart pZ (8 * cZ) (sp - K) (K + 448) ∧ Apart pZ (8 * cZ) st 24 ∧
      Outside pZ (8 * cZ) (stkWs S.mem st) := fun c0 => ZOK.ap hP hw c0 (h.dz.2.2.1 c0)
  have hdW : Apart (sp - K) (K + 448) d n :=
    ap_dst hd (fun c0 => (hzap c0).2.1.symm)
  have hdS : Apart st 24 d n := ap_dst hd (fun c0 => (hzap c0).2.2.1.symm)
  have kW : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 32 ≤ a ∧ a + k ≤ sp + 448) → m.readLE a k = S.mem.readLE a k :=
    fun a k ha => mv_rdW hP hF ha (by unfold Apart at hdW ⊢; omega)
  have hhd : HdrEq st S.mem m := by
    have hh : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = S.mem.readLE (st + j) 8 := fun j hj =>
      mv_rdH (K := K) hF hLF (by omega) (hw.sok.2.1.sub (by omega) (by omega))
        (by unfold Apart at hstw ⊢; omega) (by unfold Apart at hdS ⊢; omega)
    refine ⟨?_, hh 8 (by omega), hh 16 (by omega)⟩
    have := hh 0 (by omega); simpa using this
  have hw2 : WC R L K g sp st zp zc s.mem m L1 b1 (ℓ4 s st mp ml l1 l2) := by
    refine WC.mv hP hw hF hLF hrg hinv (by unfold Apart at hdS ⊢; omega) (fun a k ho => ?_) (fun a k hin ho => ?_)
    · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hn, c0⟩
      · simp only [outside_cons, outside_nil, and_true]; omega
      · rcases h.dz.2.2.1 c0 with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
        · simp only [ZS, outside_append, List.cons_append, List.nil_append, outside_cons, outside_nil,
            and_true] at ho ⊢
          omega
        · rw [outside_append, outside_append] at ho
          have := hin.apart ho.1.1; unfold Apart at this
          simp only [outside_cons, outside_nil, and_true]; omega
    · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hn, c0⟩
      · simp only [outside_cons, outside_nil, and_true]; omega
      · rcases h.dz.2.2.1 c0 with ⟨rfl, rfl⟩ | ⟨-, hap, -⟩
        · simp only [ZS, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
          omega
        · have := hap.apart_of_inRanges hin
          simp only [outside_cons, outside_nil, and_true]; omega
  have hrd : ∀ a k, Held R L1 a k → Apart a k (sp - K) (K + 448) → Apart a k d n → m.readLE a k = S.mem.readLE a k :=
    fun a k hh hw' hd2 => mv_rdH (K := K) hF hLF (by omega) hh hw' hd2
  have kN : ∀ {q' l c v : Nat}, LN R L s.mem st S.mem L1 q' l c v →
      (0 < c → 0 < cZ → Apart q' (8 * c) pZ (8 * cZ)) → LN R L s.mem st m L1 q' l c v := fun hq hqa =>
    LN.frm hP (LiveExt.refl R L1) hF.accessible hhd hrd hq fun c0 =>
      ap_dst hd (fun cZ0 => hqa c0 cZ0)
  subst hm
  have k8 : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 448 → S'.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a h1 h2 => kW a 8 (Or.inr ⟨by omega, h2⟩)
  refine ⟨⟨esp.trans h.jx.esp, e28.trans h.jx.e28, e29.trans h.jx.e29, e18.trans h.jx.e18, hw2,
      h.jx.esl.keep (fun a k ha => kW a k (by simp only [SlotR] at ha; omega)) (by omega), h.jx.bud⟩,
    (k8 _ (by omega) (by omega)).trans h.s288, (k8 _ (by omega) (by omega)).trans h.s208,
    (k8 _ (by omega) (by omega)).trans h.s216, (k8 _ (by omega) (by omega)).trans h.s280,
    (k8 _ (by omega) (by omega)).trans h.s192, (k8 _ (by omega) (by omega)).trans h.s200,
    (k8 _ (by omega) (by omega)).trans h.s264, (k8 _ (by omega) (by omega)).trans h.s152,
    (k8 _ (by omega) (by omega)).trans h.s160, (k8 _ (by omega) (by omega)).trans h.s256,
    (k8 _ (by omega) (by omega)).trans h.s136, (k8 _ (by omega) (by omega)).trans h.s144,
    (k8 _ (by omega) (by omega)).trans h.s272, (k8 _ (by omega) (by omega)).trans h.s168,
    (k8 _ (by omega) (by omega)).trans h.s176,
    kN h.m1 (fun _ c0 => (h.Za1 c0).symm), h.c1p,
    kN h.m2 (fun _ c0 => (h.Za2 c0).symm), h.ap,
    kN h.z1 (fun c0 cZ0 => (h.Zz1 cZ0 c0).symm), h.pz64, h.z1e, h.za1, h.za2,
    kN h.z2 (fun c0 cZ0 => (h.Zz2 cZ0 c0).symm), h.pw64, h.wa1, h.wa2, h.wz,
    DZ.frm (LiveExt.refl R L1) hF.accessible hhd h.dz, h.pZ64, h.Za1, h.Za2, h.Zz1, h.Zz2⟩

end

end FvModexp.Arm64.ExpEven
