import FvModexp.Proofs.Arm64.Witness.StubsGrow

/-! # The general `growslice` stub (arm64): allocation, copy and the live return; the contract at any address -/

namespace FvModexp.Arm64.Stubs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.RelocArm64

/-- The precondition of `GrowsliceLiveContract` with the request address `a` free. -/
@[reducible] def GPre (R : RtInv) (a : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
    LiveAt R a (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 5)

/-- Its postcondition. -/
@[reducible] def GPost (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (s s' : State) : Prop :=
  LiveAllocRet R 4096 5
      (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
      L b (growsliceRound s) (growsliceRound s) s s' fun m ptr =>
        growsliceObj R.rt s m ptr ∧ ApartAll ptr (growsliceRound s) L

set_option maxHeartbeats 1000000 in
theorem bytes_of_frame {m m' : Memory} {ws : List (Nat × Nat)} (h : MemFrame m m' ws) {x : Nat}
    (hx : Outside x 1 ws) : m'.bytes x = m.bytes x := by
  have := h.readLE x 1 hx
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

set_option maxHeartbeats 1000000 in
theorem g_alloc (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (a : Nat) (L : List (Nat × Nat))
    (b : Nat) (s U : State) (pre : GPre (toyR tys ok) a L b s) (hpc : U.pc = BitVec.ofNat 64 gALLOC)
    (hP : Pre0 s U)
    (h9 : (U.regs 9).toNat = roundupsize (8 * nextslicecap (s.regs 1).toNat (s.regs 2).toNat) true) :
    ReachesRet grProg (s.regs 30) U (GPost (toyR tys ok) L b s) := by
  obtain ⟨⟨⟨hcall, htyok, hsz, hpb, h31, h1n3, h21, hn40⟩, hold⟩, hroom, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨⟨hsp, h18, h28, h29, h30, hdz, htp, hfc, hfs⟩, hm, h0, h1, h2, h3⟩ := hP
  have hacB := LiveSat.bump_acc hinv
  have hK8 : 8 * growCap8 (s.regs 1).toNat (s.regs 2).toNat = (U.regs 9).toNat := by rw [h9, round_eq]
  janus_run until [gCPY]
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hcostK : (U.regs 9).toNat ≤ b := by
    have : growsliceRound s = (U.regs 9).toNat := by simp only [growsliceRound]; exact hK8
    rw [← this]; exact hcost
  have hc1 := le_nextslicecap (s.regs 1).toNat (s.regs 2).toNat
  have hc2 := le_roundupsize (8 * nextslicecap (s.regs 1).toNat (s.regs 2).toNat) true
  have hKpos : 8 * (s.regs 1).toNat ≤ (U.regs 9).toNat := by rw [h9]; omega
  have hdst : s.mem.accessible (s.mem.readLE 4194304 8) (8 * ((s.regs 1).toNat - (s.regs 3).toNat)) true = true :=
    LiveStub.toy_heap_acc hinvT (by omega)
  have hpb : s.mem.readLE 4194304 8 + (U.regs 9).toNat ≤ 2 ^ 48 := LiveStub.toy_heap_bound hinvT hcostK
  have hsrc : 8 * ((s.regs 1).toNat - (s.regs 3).toNat) = 0 ∨
      s.mem.accessible (s.regs 0).toNat (8 * ((s.regs 1).toNat - (s.regs 3).toNat)) false = true := by
    rcases Nat.eq_zero_or_pos ((s.regs 1).toNat - (s.regs 3).toNat) with h | h
    · left; omega
    · right; exact (hold h).2.1
  have hsrc48 : 0 < 8 * ((s.regs 1).toNat - (s.regs 3).toNat) →
      (s.regs 0).toNat + 8 * ((s.regs 1).toNat - (s.regs 3).toNat) ≤ 2 ^ 48 := fun h => (hold (by omega)).1
  refine g_copy s _ (U.regs 9) 4194304#64 (BitVec.ofNat 64 (s.mem.readLE 4194304 8)) (s.mem.readLE 4194304 8)
    (s.regs 0).toNat (8 * ((s.regs 1).toNat - (s.regs 3).toNat))
    hsrc hdst hsrc48 rfl (by ck_tac) rfl (by simp [setReg]; omega) (by simp [setReg])
    (by simp [setReg, BitVec.toNat_shiftLeft, BitVec.toNat_sub, Nat.shiftLeft_eq]; omega) ?_
  intro T hpcT hCK hMF hCp
  obtain ⟨⟨hsp', h18', h28', h29', h30', hdz', htp', hfc', hfs'⟩, hK1, hK9, hK10, hK11⟩ := hCK
  have hacB' : T.mem.accessible 4194304 8 true = true := by rw [hMF.accessible]; exact hacB
  have h30b : (T.regs 30).toNat < 2 ^ 48 := by rw [h30']; exact hcall.2.1
  have h30a : (T.regs 30).toNat % 4 = 0 := by rw [h30']; exact hcall.1
  janus_run
  obtain ⟨p, hpm, hH, h16, hend, hMF1, hLF1, hap1, hz1, hacc1, hinv1⟩ :=
    toy_alloc hty (A := 16 * (U.regs 9).toNat) (K := (U.regs 9).toNat) (by omega) (by omega) (by omega) hcostK hinvT
  have hpm' : s.mem.readLE 4194304 8 = p := hpm
  simp only [BUMP] at hMF1 hLF1 hz1 hacc1 hinv1
  simp only [hpm'] at hMF hCp hpb hdst ⊢
  clear hinv hinvT hcost hsrc hdst
  generalize hKd : (U.regs 9).toNat = K at *
  generalize hob : 8 * ((s.regs 1).toNat - (s.regs 3).toNat) = ob at *
  have hobK : ob ≤ K := by omega
  have hHB : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  -- the final memory agrees with the allocator's memory outside the copied range
  have hm31 : ∀ x, (x < p ∨ p + ob ≤ x) →
      (T.mem.writeLE 4194304 8 (p + 16 * K)).bytes x = (s.mem.writeLE 4194304 8 (p + 16 * K)).bytes x := by
    intro x hx
    by_cases hb : 4194304 ≤ x ∧ x < 4194304 + 8
    · rw [Memory.bytes_writeLE_inside _ hb.1 hb.2, Memory.bytes_writeLE_inside _ hb.1 hb.2]
    · rw [Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega),
        bytes_of_frame hMF (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hacc3 : ∀ a n w, (T.mem.writeLE 4194304 8 (p + 16 * K)).accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [Memory.accessible_writeLE, hMF.accessible]
  have hMF13 : MemFrame (s.mem.writeLE 4194304 8 (p + 16 * K)) (T.mem.writeLE 4194304 8 (p + 16 * K)) [(p, p + ob)] := by
    refine ⟨fun a k hout => Memory.readLE_congr fun i hi => ?_, fun a k w => ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at hout
      exact hm31 (a + i) (by omega)
    · rw [hacc3, Memory.accessible_writeLE]
  have hpK : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hround : growsliceRound s = K := by simp only [growsliceRound]; omega
  have hpn : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat]; omega
  unfold GPost; rw [hround]
  refine ⟨BitVec.ofNat 64 p, _, _, _, _, _, _, retStateX_eq rfl rfl ?_ ?_ ?_ ?_ ?_ rfl rfl ?_, ?fr, ?lf, ⟨⟨?fresh, ?cp, ?zb⟩, by rw [hpn]; exact hap1⟩,
    ?apw, ?inv⟩
  · simp [setReg, h18']
  · simp [setReg, h28']
  · simp [setReg, h29']
  · exact hdz'
  · exact htp'
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | i
    · simp [setReg]
    · simp [setReg, hK1]
    · simp only [setReg]; simp; congr 1; omega
    · omega
  case fr =>
    refine ⟨fun a k hout => ?_, fun a k w => hacc3 a k w⟩
    have hrt : Outside a k (toyRt tys) := by simp only [outside_append] at hout; exact hout.1
    have hHB' := LiveStub.outside_toyRt_heap_bump hrt
    refine Memory.readLE_congr fun i hi => ?_
    rw [hm31 _ (by simp only [HEND, HEAP, HSIZE] at hHB' hpK hH; omega), Memory.bytes_writeLE_outside _ (by simp [BUMP] at hHB' ⊢; omega)]
  case lf =>
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap1 r hr
    unfold Apart at hA
    rw [← hLF1.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    exact Memory.readLE_congr fun i hi => hm31 _ (by omega)
  case fresh =>
    rw [hpn]
    refine ⟨inRanges_heap hH (by omega), by simp only [HEND, HEAP, HSIZE] at hpK ⊢; omega, ?_, fun _ => by omega,
      fun _ _ => h16, fun h => absurd h (by simp), by omega⟩
    rw [hacc3]; rw [Memory.accessible_writeLE] at hacc1
    exact Memory.accessible_mono _ hacc1 (Nat.le_refl _) (by omega)
  case cp =>
    rw [hpn]
    intro i hi
    rw [Memory.bytes_writeLE_outside _ (by simp [HEAP] at hH; omega)]
    exact hCp i (by omega)
  case zb =>
    rw [hpn]
    intro i hi
    rw [show p + 8 * (s.regs 1).toNat + i = p + (8 * (s.regs 1).toNat + i) by omega, hm31 _ (by omega)]
    exact hz1 _ (by omega)
  case apw => rw [hpn]; exact apart_win (inRanges_heap (tys := tys) hH hpK) hWs
  case inv =>
    rw [hpn]
    exact RtInv.inv_frame' (R := toyR tys ok) hMF13 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Or.inr ⟨(p, p + K), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by simp; omega⟩) hinv1

/-- **`GrowsliceLiveContract` for the general stub at `E0`**, request address `a` free, any toy runtime. -/
theorem grow_sum_E0 (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (a : Nat) (L : List (Nat × Nat))
    (b : Nat) : Summary grProg E0 (GPre (toyR tys ok) a L b) (GPost (toyR tys ok) L b) := by
  intro s hpc pre
  have pre0 := pre
  obtain ⟨⟨⟨hcall, -, -, -, h31, h1n3, h21, hn40⟩, -⟩, -⟩ := pre
  have hle := le_nextslicecap (s.regs 1).toNat (s.regs 2).toNat
  have hle2 := nsc_le (s.regs 1).toNat (s.regs 2).toNat h21
  exact nsc_entry s hpc h21 hn40.1 fun T hT hpcT h5 =>
    chain s T _ hpcT hT h5 (by omega) (by omega) fun U hU hpcU h9 => g_alloc tys hty ok a L b s U pre0 hpcU hU h9

set_option maxRecDepth 100000 in
theorem grCode_ok : CodeOK E0 grCode = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem grCode_len : grCode.length = 252 := by decide

/-- **`GrowsliceLiveContract` for the general stub `grCode` placed at `a` in `p`** (any toy runtime `toyR tys ok`). -/
theorem growslice_live_at (p : Program) (a : Nat) (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hfit : a + 4 * 252 < 2 ^ 64) (hf : FetchedAt grCode p a) : GrowsliceLiveContract p a 4096 (toyR tys ok) := by
  intro L b
  refine summary_transport E0 a grCode p _ _ (by rw [grCode_len]; decide) grCode_ok (by rw [grCode_len]; decide)
    (by rw [grCode_len]; exact hfit) hf ?_ ?_ (fun s s' q h => by exact h) (grow_sum_E0 tys hty ok a L b)
  · intro t ht
    have : (t.regs 30).toNat < 2 ^ 48 := ht.1.1.1.2.1
    simp only [E0]; omega
  · intro s q h
    exact h

end FvModexp.Arm64.Stubs
