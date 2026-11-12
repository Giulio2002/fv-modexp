import FvModexp.Proofs.Arm64.Nat.DivLargeRelB

/-!
# `divLarge` (arm64): preconditions of the live runtime calls after `u.make` (pure)

`rt_pre`: `CallOK`/`StackRoom`/`LiveAt` at a call state `S` with `SP = entry SP - 304` (Janus `call_pre` with the base
state `{S with sp := s.sp}`); `mv_pre` (`runtime.memmove`), `mc_pre` (`runtime.memclrNoHeapPointers`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivLarge

set_option maxHeartbeats 4000000 in
theorem rt_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1)
    {Lk : List (Nat × Nat)} {bk : Nat} (hx : LiveExt R L1 Lk) (S : State) (hsp : S.sp = s.sp - 304#64)
    (h28 : S.regs 28 = s.regs 28)
    (hgrd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) (addr : Nat) (args : List Nat) (nargs : Nat)
    (hn : nargs ≤ 3) (hok : R.ok addr args) :
    CallOK S 4096 nargs ∧ StackRoom S 4096 nargs ∧
      LiveAt R addr args Lk bk 0 (S.regs 28).toNat S.mem (calleeStack S 4096 nargs) ∧ S.sp.toNat = s.sp.toNat - 304 := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hE.pre.ce
  unfold Apart at hga
  have hspn : S.sp.toNat = s.sp.toNat - 304 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hLs := lsep_of hE hx
  have e1 : s.sp.toNat + 112 - (s.sp.toNat - 41264) = 41264 + 112 := by omega
  have hw' : S.mem.accessible (s.sp.toNat - 41264) (s.sp.toNat + 112 - (s.sp.toNat - 41264)) true = true := by
    rw [hacc, e1]; exact hw
  have hc := call_pre R Lk bk 0 addr args (s := { S with sp := s.sp }) (S := S) (lo := s.sp.toNat - 41264)
    (hi := s.sp.toNat + 112) (stack := 4096) (nargs := nargs) (fr := 304)
    (by rw [h28]; exact hg1) (by simp only; rw [h28, hacc]; exact hg2) (by simp only; rw [h28, hgrd]; omega)
    (by simp only [outside_cons]; rw [h28]; exact ⟨by omega, hgr⟩) ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩ rfl (by simp only; omega) (by rw [hspn]; omega) h30a h30b (by decide) (by omega) (by omega)
    (by omega) (by omega) hw'
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [e1]; exact hout)
    (fun r hr => by have := hLs r hr; simp only [outside_cons, outside_nil, and_true]; omega)
    hok (by rw [h28]; exact hinv) (Nat.zero_le _)
  exact ⟨hc.1, hc.2.1, hc.2.2, hspn⟩

set_option maxHeartbeats 4000000 in
/-- `runtime.memmove(dst, src, n)` at `S` -/
theorem mv_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1)
    {Lk : List (Nat × Nat)} {bk : Nat} (hx : LiveExt R L1 Lk) (S : State) (hsp : S.sp = s.sp - 304#64)
    (h28 : S.regs 28 = s.regs 28)
    (hgrd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) {dst src n : Nat}
    (h0 : (S.regs 0).toNat = dst) (h1 : (S.regs 1).toNat = src) (h2 : (S.regs 2).toNat = n)
    (hok : R.ok (cA "runtime.memmove") [dst, src, n])
    (hd48 : dst + n ≤ 2 ^ 48) (hdacc : S.mem.accessible dst n true = true) (hdh : Held R Lk dst n)
    (hdw : dst + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ dst)
    (hs48 : src + n ≤ 2 ^ 48) (hsacc : S.mem.accessible src n false = true)
    (hsw : src + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ src) :
    Mem.EqPre 4096 3 S ∧
      LiveMemAt R (cA "runtime.memmove") [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat] Lk bk S
        (calleeStack S 4096 3) ∧
      Mem.Input S 4096 3 (S.regs 1).toNat (S.regs 2).toNat ∧ LiveDest R Lk S 4096 3 (S.regs 0).toNat (S.regs 2).toNat := by
  have hl := hE.lay
  have hsp0 := hl.sp0
  rw [h0, h1, h2]
  obtain ⟨hco, ⟨hgk, hgout⟩, ⟨hok', hinv', -, hs1, hs2⟩, hspn⟩ :=
    rt_pre hE hx S hsp h28 hgrd hacc h30a h30b hinv _ _ 3 (by omega) hok
  refine ⟨⟨(guardOK_iff _ _).1 hgk, hco, hgout⟩, ⟨hok', hinv', hs1, hs2⟩, ⟨hs48, hsacc, ?_⟩, ⟨hd48, hdacc, ?_, hdh⟩⟩
  · simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  · simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [hspn]; omega

set_option maxHeartbeats 4000000 in
/-- `runtime.memclrNoHeapPointers(ptr, n)` at `S` -/
theorem mc_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1)
    {Lk : List (Nat × Nat)} {bk : Nat} (hx : LiveExt R L1 Lk) (S : State) (hsp : S.sp = s.sp - 304#64)
    (h28 : S.regs 28 = s.regs 28)
    (hgrd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) {dst n : Nat}
    (h0 : (S.regs 0).toNat = dst) (h1 : (S.regs 1).toNat = n)
    (hok : R.ok (cA "runtime.memclrNoHeapPointers") [dst, n])
    (hd48 : dst + n ≤ 2 ^ 48) (hdacc : S.mem.accessible dst n true = true) (hdh : Held R Lk dst n)
    (hdw : dst + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ dst) :
    Mem.EqPre 4096 2 S ∧
      LiveMemAt R (cA "runtime.memclrNoHeapPointers") [(S.regs 0).toNat, (S.regs 1).toNat] Lk bk S
        (calleeStack S 4096 2) ∧
      LiveDest R Lk S 4096 2 (S.regs 0).toNat (S.regs 1).toNat := by
  have hl := hE.lay
  have hsp0 := hl.sp0
  rw [h0, h1]
  obtain ⟨hco, ⟨hgk, hgout⟩, ⟨hok', hinv', -, hs1, hs2⟩, hspn⟩ :=
    rt_pre hE hx S hsp h28 hgrd hacc h30a h30b hinv _ _ 2 (by omega) hok
  refine ⟨⟨(guardOK_iff _ _).1 hgk, hco, hgout⟩, ⟨hok', hinv', hs1, hs2⟩, ⟨hd48, hdacc, ?_, hdh⟩⟩
  simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [hspn]; omega

/-- the stack guard word is unchanged after `stk.nat` (pure) -/
theorem Mem.grd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory}
    (hM : Mem R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk M) :
    M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
  have hga := hE.pre.ce.2.2.2.2.1; have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.1
  unfold Apart at hga
  have hk : Outside ((s.regs 28).toNat + 16) 8 (stkWs s.mem st) :=
    outside_stkWs hE.pre (hE.pre.sti.2.2.1.symm) fun hc => (hE.pre.sti.2.2.2 hc).2.symm
  refine hM.fr.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨⟨hgr, ?_⟩, g_wsL hE⟩, hk⟩
  simp only [winA, outside_cons, outside_nil, and_true]; omega

/-- the top word of a nat from its value -/
theorem top_of_natVal (m : Memory) (p n : Nat) (hn : 1 ≤ n) :
    m.readLE (p + 8 * (n - 1)) 8 = natVal m p n / 2 ^ (64 * (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [natVal_succ]
  have hlo : natVal m p k < 2 ^ (64 * k) := by
    unfold natVal; have := Memory.readLE_lt m p (8 * k); rw [show (256 : Nat) ^ (8 * k) = 2 ^ (64 * k) by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this; exact this
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.zero_add]

end FvModexp.Arm64.DivLarge
