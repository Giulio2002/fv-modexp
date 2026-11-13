import FvModexp.Proofs.Arm64.Nat.DrsPro2
import FvModexp.Proofs.Arm64.Nat.NatAddMid

/-!
# `divRecursiveStep` (arm64): preconditions of the live runtime calls (pure)

`rt_pre`: `CallOK`/`StackRoom`/`LiveAt` at a call state `S` with `SP = entry SP - 400` (Janus `call_pre` with the base
state `{S with sp := s.sp}`; window `W ≥ 4608` of the entry's `CallEnv`); `mc_pre` (`runtime.memclrNoHeapPointers`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.NatAdd (outside_of_inRanges)

/-- every live object (after runtime allocations) is outside the window -/
theorem lsep {R : RtInv} {L Lk : List (Nat × Nat)} {s : State} {W : Nat} (hce : CallEnv R L s W 96)
    (hx : LiveExt R L Lk) : ∀ r ∈ Lk, r.1 + (r.2 - r.1) ≤ s.sp.toNat - W ∨ s.sp.toNat + 96 ≤ r.1 := by
  obtain ⟨-, -, -, hout, -, -, hLs, -⟩ := hce
  rcases hx with ⟨ns, rfl, hn, -⟩
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  · have := outside_of_inRanges hout (hn r hr).1; omega

set_option maxHeartbeats 4000000 in
theorem rt_pre {R : RtInv} {L : List (Nat × Nat)} {s : State} {W : Nat} (hce : CallEnv R L s W 96) (hW : 4608 ≤ W)
    {Lk : List (Nat × Nat)} {bk : Nat} (hx : LiveExt R L Lk) (S : State) (hsp : S.sp = s.sp - 400#64)
    (h28 : S.regs 28 = s.regs 28)
    (hgrd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) (addr : Nat) (args : List Nat) (nargs : Nat)
    (hn : nargs ≤ 3) (hok : R.ok addr args) :
    CallOK S 4096 nargs ∧ StackRoom S 4096 nargs ∧
      LiveAt R addr args Lk bk 0 (S.regs 28).toNat S.mem (calleeStack S 4096 nargs) ∧ S.sp.toNat = s.sp.toNat - 400 := by
  have hLs := lsep hce hx
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  unfold Apart at hga
  have hspn : S.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have e1 : s.sp.toNat + 96 - (s.sp.toNat - W) = W + 96 := by omega
  have hw' : S.mem.accessible (s.sp.toNat - W) (s.sp.toNat + 96 - (s.sp.toNat - W)) true = true := by
    rw [hacc, e1]; exact hw
  have hc := call_pre R Lk bk 0 addr args (s := { S with sp := s.sp }) (S := S) (lo := s.sp.toNat - W)
    (hi := s.sp.toNat + 96) (stack := 4096) (nargs := nargs) (fr := 400)
    (by rw [h28]; exact hg1) (by simp only; rw [h28, hacc]; exact hg2) (by simp only; rw [h28, hgrd]; omega)
    (by simp only [outside_cons]; rw [h28]; exact ⟨by omega, hgr⟩) ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩ rfl
    (by simp only; omega) (by rw [hspn]; omega) h30a h30b (by decide) (by omega) (by omega)
    (by omega) (by omega) hw'
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [e1]; exact hout)
    (fun r hr => by have := hLs r hr; simp only [outside_cons, outside_nil, and_true]; omega)
    hok (by rw [h28]; exact hinv) (Nat.zero_le _)
  exact ⟨hc.1, hc.2.1, hc.2.2, hspn⟩

set_option maxHeartbeats 4000000 in
/-- `runtime.memclrNoHeapPointers(ptr, n)` at `S` -/
theorem mc_pre {R : RtInv} {L : List (Nat × Nat)} {s : State} {W : Nat} (hce : CallEnv R L s W 96) (hW : 4608 ≤ W)
    {Lk : List (Nat × Nat)} {bk : Nat} (hx : LiveExt R L Lk) (S : State) (hsp : S.sp = s.sp - 400#64)
    (h28 : S.regs 28 = s.regs 28)
    (hgrd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk S.mem)) {dst n : Nat}
    (h0 : (S.regs 0).toNat = dst) (h1 : (S.regs 1).toNat = n)
    (hok : R.ok (cA "runtime.memclrNoHeapPointers") [dst, n])
    (hd48 : dst + n ≤ 2 ^ 48) (hdacc : S.mem.accessible dst n true = true) (hdh : Held R Lk dst n)
    (hdw : dst + n ≤ s.sp.toNat - W ∨ s.sp.toNat + 96 ≤ dst) :
    Mem.EqPre 4096 2 S ∧
      LiveMemAt R (cA "runtime.memclrNoHeapPointers") [(S.regs 0).toNat, (S.regs 1).toNat] Lk bk S
        (calleeStack S 4096 2) ∧
      LiveDest R Lk S 4096 2 (S.regs 0).toNat (S.regs 1).toNat := by
  have hsp0 : W ≤ s.sp.toNat := by obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce; omega
  rw [h0, h1]
  obtain ⟨hco, ⟨hgk, hgout⟩, ⟨hok', hinv', -, hs1, hs2⟩, hspn⟩ :=
    rt_pre hce hW hx S hsp h28 hgrd hacc h30a h30b hinv _ _ 2 (by omega) hok
  refine ⟨⟨(guardOK_iff _ _).1 hgk, hco, hgout⟩, ⟨hok', hinv', hs1, hs2⟩, ⟨hd48, hdacc, ?_, hdh⟩⟩
  simp only [calleeStack, outside_cons, outside_nil, and_true]; rw [hspn]; omega

end FvModexp.Arm64.DivRec
