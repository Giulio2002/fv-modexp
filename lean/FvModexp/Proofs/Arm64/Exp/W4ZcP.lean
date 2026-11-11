import FvModexp.Proofs.Arm64.Exp.W4ZcDefs

/-!
# window-4 prologue (arm64): bookkeeping after the first-window `memmove` (pure)

From the `memmove` post (frame over the spill chain, `Mem.Copied`), the slot reads and frames `W4ZcC.zcC` takes.
Kept out of `W4ZcB` so that the run's large context does not slow the reads down.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the spill chain at the first-window `memmove` -/
@[reducible] def zcW (M : Memory) (sp zc zp ylen yi zzc zzp k : Nat) : Memory :=
  ((((((((M.writeLE (sp + 144) 8 zc).writeLE (sp + 368) 8 zp).writeLE (sp + 240) 8 (ylen - 1)).writeLE (sp + 184) 8
    yi).writeLE (sp + 296) 8 zzc).writeLE (sp + 872) 8 zzp).writeLE (sp + 328) 8 (k + 1)).writeLE (sp + 232) 8 k)

set_option maxHeartbeats 64000000 in
theorem zcPost {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc k0 yp ylen zp zc zzp zzc yi k pd V : Nat}
    {M m1 : Memory} (he : Env R L g sp M) (hz : Buf R L g sp n M zp zc) (hk : k ≤ 15)
    (hzzc' : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi64 : yi < 2 ^ 64)
    (hpb : Apart pd (8 * n) (sp - 4288) (4288 + 1040)) (hvd : M.readLE pd (8 * n) = V)
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r1016 : M.readLE (sp + 1016) 8 = mp)
    (r1032 : M.readLE (sp + 1032) 8 = mc)
    (hF1 : MemFrame (zcW M sp zc zp ylen yi zzc zzp k) m1
      (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 8 + 24)] ++ [(zp, zp + 8 * n)]))
    (hL1 : LiveFrame (zcW M sp zc zp ylen yi zzc zzp k) m1 L [(zp, zp + 8 * n)])
    (hC1 : Mem.Copied (zcW M sp zc zp ylen yi zzc zzp k) m1 zp pd (8 * n)) :
    m1.readLE (sp + 368) 8 = zp ∧ m1.readLE (sp + 872) 8 = zzp ∧ m1.readLE (sp + 1024) 8 = n ∧
    m1.readLE (sp + 144) 8 = zc ∧ m1.readLE (sp + 296) 8 = zzc ∧ m1.readLE (sp + 1000) 8 = ylen ∧
    m1.readLE (sp + 240) 8 = ylen - 1 ∧ m1.readLE (sp + 992) 8 = yp ∧ m1.readLE (sp + 184) 8 = yi ∧
    m1.readLE (sp + 328) 8 = k + 1 ∧ m1.readLE (sp + 232) 8 = k ∧ m1.readLE (sp + 224) 8 = k0 ∧
    m1.readLE (sp + 1016) 8 = mp ∧ m1.readLE (sp + 1032) 8 = mc ∧
    MemFrame M m1 (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) ∧ LiveFrame M m1 L [(zp, zp + 8 * n)] ∧
    m1.readLE zp (8 * n) = V ∧ (zp + 8 * n ≤ sp + 240 ∨ sp + 248 ≤ zp) := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  unfold Apart at z6 hpb
  have rd : ∀ K, 32 ≤ K → K + 8 ≤ 1040 →
      m1.readLE (sp + K) 8 = (zcW M sp zc zp ylen yi zzc zzp k).readLE (sp + K) 8 := fun K k1 k2 =>
    hF1.readLE (sp + K) 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have w : ∀ (a v : Nat) (m : Memory), (m.writeLE a 8 v).readLE a 8 = v % 18446744073709551616 := fun a v m =>
    Memory.readLE_writeLE_self _ _ _ _
  have hLz : ∀ a k, InRanges a k L → Outside a k (cw sp) := by
    intro a k hin
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hWf : MemFrame M (zcW M sp zc zp ylen yi zzc zzp k) (cw sp) := by
    simp only [zcW]
    repeat' first
      | exact MemFrame.refl _ _
      | apply MemFrame.writeLE_inRanges
      | (simp only [InRanges, cw, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
         omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [rd 368 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 872 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 1024 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact r1024
  · rw [rd 144 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 296 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 1000 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact r1000
  · rw [rd 240 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 992 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact r992
  · rw [rd 184 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 328 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 232 (by omega) (by omega)]; simp only [zcW]; rw [w]; omega
  · rw [rd 224 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact r224
  · rw [rd 1016 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact r1016
  · rw [rd 1032 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]; exact r1032
  · exact mf_chain (M := M) (W := cw sp) hWf hF1
      (fun a k ho => by
        simp only [cw, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨ho.1.2, ⟨ho.1.1, by omega⟩, ho.2⟩)
  · exact lf_chain (M := M) (W := cw sp) hWf hLz hL1
  · rw [FvModexp.Expmc.readLE_of_copied hC1]; simp only [zcW]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact hvd

end FvModexp.Arm64.W4Pro
