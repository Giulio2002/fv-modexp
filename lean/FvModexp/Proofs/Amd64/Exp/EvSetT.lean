import FvModexp.Proofs.Amd64.Exp.EvLZ
import FvModexp.Proofs.Amd64.Exp.EvMv

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the tail of `z = z.set(z2)` — `setJ` → `mvJ` (asm s61; twin of infra's arm64 `EvSetT`)

nat.go:93-94 (`copy(z, z2)` of the inlined `set`): at `setJ` (`JS`) `z`'s array `(pZ, cZ)` is chosen (entry `z`
reused, or a fresh `makeslice`), `DZ` = `LZ` without the value. `runJ` spills `z` (`0x108/0xa0/0xa8`; `JO` = the facts
after these stores) and either skips the copy (same pointer, `JE`) or calls `memmove(pZ, pw, 8·lw)` (`mvCall`; an empty
copy reports the written range `[0, 0)`). `JO.toJ9`, `JO.mv`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the return state of a call (`res` results) -/
theorem rs_regs {T : State} {junk : Nat → W64} {res : List W64} {f : Flags} {x yh : Nat → BitVec 128} {m : Memory}
    {zh : Nat → BitVec 256} {kr : Nat → W64} :
    (retState64 T junk res f x yh m zh kr).regs 4 = T.regs 4 + 8#64 ∧
      (retState64 T junk res f x yh m zh kr).regs 5 = T.regs 5 ∧
      (retState64 T junk res f x yh m zh kr).regs 14 = T.regs 14 ∧
      (retState64 T junk res f x yh m zh kr).fsBase = T.fsBase ∧
      (retState64 T junk res f x yh m zh kr).xmm 15 = T.xmm 15 ∧
      (retState64 T junk res f x yh m zh kr).df = T.df ∧
      (retState64 T junk res f x yh m zh kr).rip = retAddrOf T ∧
      (retState64 T junk res f x yh m zh kr).mem = m := by
  simp [retState64, callRegs64_apply]

theorem rs_r0 {T : State} {junk : Nat → W64} {ptr : W64} {f : Flags} {x yh : Nat → BitVec 128} {m : Memory}
    {zh : Nat → BitVec 256} {kr : Nat → W64} : (retState64 T junk [ptr] f x yh m zh kr).regs 0 = ptr := by
  simp [retState64, callRegs64_apply]

/-- a call state with `RSP` reset to the frame's `sp` (the frame's view of a state at a `CALL`) -/
@[reducible] def atSp (T : State) (sp : Nat) : State := { T with regs := setRegF T.regs 4 (BitVec.ofNat 64 sp) }

theorem atSp_eqs {T : State} {sp : Nat} : (atSp T sp).regs 4 = BitVec.ofNat 64 sp ∧
    (atSp T sp).regs 14 = T.regs 14 ∧ (atSp T sp).mem = T.mem ∧ (atSp T sp).fsBase = T.fsBase ∧
    (atSp T sp).xmm 15 = T.xmm 15 ∧ (atSp T sp).df = T.df := by
  simp [atSp, setRegF_apply]

/-- the return address of a call state at `RSP = sp - 8` -/
theorem ra_eq {T : State} {sp ra : Nat} (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8)) (hsp : sp < 2 ^ 64)
    (hra : T.mem.readLE (sp - 8) 8 = ra) : retAddrOf T = BitVec.ofNat 64 ra := by
  rw [retAddrOf_eq, h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hra]

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
structure JS (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  pc : S.rip = BitVec.ofNat 64 setJ
  r0 : S.regs 0 = BitVec.ofNat 64 pw
  r1 : S.regs 1 = BitVec.ofNat 64 cw
  r3 : S.regs 3 = BitVec.ofNat 64 lw
  r6 : S.regs 6 = BitVec.ofNat 64 lw
  r7 : S.regs 7 = BitVec.ofNat 64 pZ
  r2 : S.regs 2 = BitVec.ofNat 64 cZ
  s118 : S.mem.readLE (sp + 0x118) 8 = p1
  sc8 : S.mem.readLE (sp + 0xc8) 8 = l1
  sd0 : S.mem.readLE (sp + 0xd0) 8 = c1
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  s100 : S.mem.readLE (sp + 0x100) 8 = pz
  s90 : S.mem.readLE (sp + 0x90) 8 = lz
  s98 : S.mem.readLE (sp + 0x98) 8 = cz
  sf8 : S.mem.readLE (sp + 0xf8) 8 = pw
  s80 : S.mem.readLE (sp + 0x80) 8 = lw
  s88 : S.mem.readLE (sp + 0x88) 8 = cw
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
  z2e : EL R L pw cw
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)
  dz : DZ R L st zp zc S.mem L1 pZ lw cZ
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  Za1 : 0 < cZ → Apart pZ (8 * cZ) p1 (8 * c1)
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz1 : 0 < cZ → 0 < cz → Apart pZ (8 * cZ) pz (8 * cz)
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)
  lwm : lw ≤ ml

/-- the facts after `runJ`'s spills of `z` (no pc / registers; `z` not yet copied) -/
structure JO (R : RtInv) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat) (s : State)
    (rk : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat) : Prop where
  jx : JX R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 (lvl4 s st mp ml l1 l2) rk
  s118 : S.mem.readLE (sp + 0x118) 8 = p1
  sc8 : S.mem.readLE (sp + 0xc8) 8 = l1
  sd0 : S.mem.readLE (sp + 0xd0) 8 = c1
  s110 : S.mem.readLE (sp + 0x110) 8 = q
  sb8 : S.mem.readLE (sp + 0xb8) 8 = l2
  sc0 : S.mem.readLE (sp + 0xc0) 8 = a2 ml (nE s mp ml)
  s100 : S.mem.readLE (sp + 0x100) 8 = pz
  s90 : S.mem.readLE (sp + 0x90) 8 = lz
  s98 : S.mem.readLE (sp + 0x98) 8 = cz
  sf8 : S.mem.readLE (sp + 0xf8) 8 = pw
  s80 : S.mem.readLE (sp + 0x80) 8 = lw
  s88 : S.mem.readLE (sp + 0x88) 8 = cw
  s108 : S.mem.readLE (sp + 0x108) 8 = pZ
  sa0 : S.mem.readLE (sp + 0xa0) 8 = lw
  sa8 : S.mem.readLE (sp + 0xa8) 8 = cZ
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
  z2e : EL R L pw cw
  wa1 : 0 < cw → Apart pw (8 * cw) p1 (8 * c1)
  wa2 : 0 < cw → Apart pw (8 * cw) q (8 * a2 ml (nE s mp ml))
  wz : 0 < cw → 0 < cz → Apart pw (8 * cw) pz (8 * cz)
  dz : DZ R L st zp zc S.mem L1 pZ lw cZ
  pZ64 : pZ < 2 ^ 64
  Ze : cZ = 0 → pZ = zp ∧ cZ = zc
  Za1 : 0 < cZ → Apart pZ (8 * cZ) p1 (8 * c1)
  Za2 : 0 < cZ → Apart pZ (8 * cZ) q (8 * a2 ml (nE s mp ml))
  Zz1 : 0 < cZ → 0 < cz → Apart pZ (8 * cZ) pz (8 * cz)
  Zz2 : 0 < cZ → 0 < cw → Apart pZ (8 * cZ) pw (8 * cw)



section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- `JO` + pc / registers + `z`'s value ⇒ `J9` -/
theorem JO.toJ9 {rk : Nat} {S : State} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : JO R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ)
    (hpc : S.rip = BitVec.ofNat 64 mvJ) (h0 : S.regs 0 = BitVec.ofNat 64 pw) (h1 : S.regs 1 = BitVec.ofNat 64 cw)
    (h6 : S.regs 6 = BitVec.ofNat 64 lw)
    (hv : natVal S.mem pZ lw = natVal s.mem xp xl ^ natVal s.mem yp yl % (natVal s.mem mp ml / 2 ^ nE s mp ml))
    (hn : NatNorm S.mem pZ lw) :
    J9 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ :=
  ⟨h.jx, hpc, h0, h1, h6, h.s118, h.sc8, h.sd0, h.s110, h.sb8, h.sc0, h.s100, h.s90, h.s98, h.sf8, h.s80,
    h.s88, h.s108, h.sa0, h.sa8, h.m1, h.c1p, h.m2, h.ap, h.z1, h.pz64, h.z1e, h.za1, h.za2, h.z2, h.pw64, h.z2e, h.wa1,
    h.wa2, h.wz, ⟨h.dz.1, h.dz.2.1, h.dz.2.2.1, h.dz.2.2.2, hv, hn⟩, h.pZ64, h.Ze, h.Za1, h.Za2, h.Zz1, h.Zz2⟩

/-- an apartness from `[p, p + 8c)` gives one from a destination inside it (or an empty one at `0`) -/
theorem ap_dst {p c d n a k : Nat} (hd : (d = 0 ∧ n = 0) ∨ (d = p ∧ n ≤ 8 * c ∧ 0 < c))
    (h : 0 < c → Apart a k p (8 * c)) : Apart a k d n := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hn, hc⟩
  · unfold Apart; omega
  · have := h hc; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- **`JO` through `memmove(d, ·, n)`** with `[d, d + n)` empty at `0` or inside `z`'s array: every local and slot
kept, `WC` kept; the state `S'` has the memory after the call and `S`'s `RSP` / `R14` / `fs` / `X15` / `DF` -/
theorem JO.mv (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {rk : Nat} {S : State}
    {L1 : List (Nat × Nat)} {b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ : Nat}
    (h : JO R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ)
    {d n : Nat} (hd : (d = 0 ∧ n = 0) ∨ (d = pZ ∧ n ≤ 8 * cZ ∧ 0 < cZ)) {m : Memory}
    (hF : MemFrame S.mem m (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp, sp + 24)] ++ [(d, d + n)]))
    (hLF : LiveFrame S.mem m L1 [(d, d + n)]) (hrg : m.regions = S.mem.regions)
    (hinv : R.inv b1 L1 g (view R.rt L1 m)) (S' : State) (esp : S'.regs 4 = S.regs 4)
    (e14 : S'.regs 14 = S.regs 14) (efs : S'.fsBase = S.fsBase) (ex15 : S'.xmm 15 = S.xmm 15) (edf : S'.df = S.df)
    (hm : S'.mem = m) :
    JO R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s rk S' L1 b1 p1 l1 c1 q l2 pz lz cz pw lw cw pZ cZ := by
  have hk := hP.kf
  have hstw := hP.stkF.1
  have hw := h.jx.wc
  -- the destination is apart from the window, the header; inside what the function may write
  have hzap : 0 < cZ → Held R L1 pZ (8 * cZ) ∧ Apart pZ (8 * cZ) (sp - 8 - K) (K + 0x1c0) ∧ Apart pZ (8 * cZ) st 24 ∧
      Outside pZ (8 * cZ) (stkWs S.mem st) := fun c0 => ZOK.ap hP hw c0 (h.dz.2.2.1 c0)
  have hdW : Apart (sp - 8 - K) (K + 0x1c0) d n :=
    ap_dst hd (fun c0 => (hzap c0).2.1.symm)
  have hdS : Apart st 24 d n := ap_dst hd (fun c0 => (hzap c0).2.2.1.symm)
  have kW : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp ∨ sp + 24 ≤ a ∧ a + k ≤ sp + 0x1b8) → m.readLE a k = S.mem.readLE a k :=
    fun a k ha => mv_rdW hP hF ha (by unfold Apart at hdW ⊢; omega)
  have hhd : HdrEq st S.mem m := by
    have hh : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = S.mem.readLE (st + j) 8 := fun j hj =>
      mv_rdH (K := K) hF hLF (by omega) (hw.sok.2.1.sub (by omega) (by omega))
        (by unfold Apart at hstw ⊢; omega) (by unfold Apart at hdS ⊢; omega)
    refine ⟨?_, hh 8 (by omega), hh 16 (by omega)⟩
    have := hh 0 (by omega); simpa using this
  have hw2 : WC R L K g sp st zp zc s.mem m L1 b1 (lvl4 s st mp ml l1 l2) := by
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
  have hrd : ∀ a k, Held R L1 a k → Apart a k (sp - 8 - K) (K + 0x1c0) → Apart a k d n →
      m.readLE a k = S.mem.readLE a k :=
    fun a k hh hw' hd2 => mv_rdH (K := K) hF hLF (by omega) hh hw' hd2
  have kN : ∀ {q' l c v : Nat}, LN R L s.mem st S.mem L1 q' l c v →
      (0 < c → 0 < cZ → Apart q' (8 * c) pZ (8 * cZ)) → LN R L s.mem st m L1 q' l c v := fun hq hqa =>
    LN.frm hP (LiveExt.refl R L1) hF.accessible hhd hrd hq fun c0 =>
      ap_dst hd (fun cZ0 => hqa c0 cZ0)
  subst hm
  have k8 : ∀ a, sp + 0x78 ≤ a → a + 8 ≤ sp + 0x1b8 → S'.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a h1 h2 => kW a 8 (Or.inr ⟨by omega, h2⟩)
  refine ⟨h.jx.call esp e14 efs ex15 edf hw2 (fun a k h1 h2 => kW a k (Or.inr ⟨by omega, h2⟩)) h.jx.bud,
    (k8 _ (by omega) (by omega)).trans h.s118, (k8 _ (by omega) (by omega)).trans h.sc8,
    (k8 _ (by omega) (by omega)).trans h.sd0, (k8 _ (by omega) (by omega)).trans h.s110,
    (k8 _ (by omega) (by omega)).trans h.sb8, (k8 _ (by omega) (by omega)).trans h.sc0,
    (k8 _ (by omega) (by omega)).trans h.s100, (k8 _ (by omega) (by omega)).trans h.s90,
    (k8 _ (by omega) (by omega)).trans h.s98, (k8 _ (by omega) (by omega)).trans h.sf8,
    (k8 _ (by omega) (by omega)).trans h.s80, (k8 _ (by omega) (by omega)).trans h.s88,
    (k8 _ (by omega) (by omega)).trans h.s108, (k8 _ (by omega) (by omega)).trans h.sa0,
    (k8 _ (by omega) (by omega)).trans h.sa8,
    kN h.m1 (fun _ c0 => (h.Za1 c0).symm), h.c1p,
    kN h.m2 (fun _ c0 => (h.Za2 c0).symm), h.ap,
    kN h.z1 (fun c0 cZ0 => (h.Zz1 cZ0 c0).symm), h.pz64, h.z1e, h.za1, h.za2,
    kN h.z2 (fun c0 cZ0 => (h.Zz2 cZ0 c0).symm), h.pw64, h.z2e, h.wa1, h.wa2, h.wz,
    DZ.frm (LiveExt.refl R L1) hF.accessible hhd h.dz, h.pZ64, h.Ze, h.Za1, h.Za2, h.Zz1, h.Zz2⟩

end

end FvModexp.Amd64.ExpEven
