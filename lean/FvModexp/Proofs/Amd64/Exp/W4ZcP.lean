import FvModexp.Proofs.Amd64.Exp.W4ZcDefs

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the facts after the first-window `memmove` (agent expmc s48)

Twin of `Arm64.W4ZcP`. The spills before `CALL runtime.memmove` (+0xc58..+0xc78, return address `+0xc8f`) and the
memmove contract's frame give the slot reads the tail (+0xc8f → loop test) needs, the frame from the `zj` memory `M`,
and the copied value. Small context, no run.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf)

/-- the spill chain at the first-window `memmove` -/
@[reducible] def zcW (M : Memory) (sp zzc zzp yi k : Nat) : Memory :=
  (((((M.writeLE (sp + 288) 8 zzc).writeLE (sp + 880) 8 zzp).writeLE (sp + 280) 8 yi).writeLE (sp + 320) 8 (k + 1)).writeLE
    (sp + 312) 8 (k * 4)).writeLE (sp - 8) 8 6208751

/-- the slot reads after the copy -/
@[reducible] def ZcSl (m : Memory) (sp n mp mc k0 yp ylen zp zc zzp zzc yi k : Nat) : Prop :=
  m.readLE (sp + 0x168) 8 = zp ∧ m.readLE (sp + 0x138) 8 = k * 4 ∧ m.readLE (sp + 0x88) 8 = zc ∧
  m.readLE (sp + 0x390) 8 = yp ∧ m.readLE (sp + 0x370) 8 = zzp ∧ m.readLE (sp + 0x118) 8 = yi ∧
  m.readLE (sp + 0x120) 8 = zzc ∧ m.readLE (sp + 0x398) 8 = ylen ∧ m.readLE (sp + 0x140) 8 = k + 1 ∧
  m.readLE (sp + 0x3a8) 8 = mp ∧ m.readLE (sp + 0xd8) 8 = k0 ∧ m.readLE (sp + 0x3b0) 8 = n ∧
  m.readLE (sp + 0x3b8) 8 = mc

set_option maxHeartbeats 64000000 in
theorem zcPost {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi k pd V : Nat}
    {M m1 : Memory} (he : Env R L g fs sp M) (hz : Buf R L g fs sp n M zp zc) (hk : k ≤ 15)
    (hzzc : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64) (hyi64 : yi < 2 ^ 64)
    (hpb : Apart pd (8 * n) (sp - 4296) (4296 + 0x3c0)) (hvd : M.readLE pd (8 * n) = V)
    (r168 : M.readLE (sp + 0x168) 8 = zp) (r88 : M.readLE (sp + 0x88) 8 = zc)
    (r398 : M.readLE (sp + 0x398) 8 = ylen) (r390 : M.readLE (sp + 0x390) 8 = yp)
    (r3a8 : M.readLE (sp + 0x3a8) 8 = mp) (rd8 : M.readLE (sp + 0xd8) 8 = k0) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (r3b8 : M.readLE (sp + 0x3b8) 8 = mc)
    (hF1 : MemFrame (zcW M sp zzc zzp yi k) m1
      (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(zp, zp + 8 * n)]))
    (hL1 : LiveFrame (zcW M sp zzc zzp yi k) m1 L [(zp, zp + 8 * n)])
    (hC1 : Mem.Copied (zcW M sp zzc zzp yi k) m1 zp pd (8 * n)) :
    ZcSl m1 sp n mp mc k0 yp ylen zp zc zzp zzc yi k ∧
    MemFrame M m1 (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) ∧ LiveFrame M m1 L [(zp, zp + 8 * n)] ∧
    m1.readLE zp (8 * n) = V := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, -⟩ := he
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  unfold Apart at z6 hpb
  have rd : ∀ K, 0x88 ≤ K → K + 8 ≤ 0x3c0 →
      m1.readLE (sp + K) 8 = (zcW M sp zzc zzp yi k).readLE (sp + K) 8 := fun K k1 k2 =>
    hF1.readLE (sp + K) 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have w : ∀ (a v : Nat) (m : Memory), (m.writeLE a 8 v).readLE a 8 = v % 18446744073709551616 := fun a v m =>
    Arm64.Memory.readLE_writeLE_self _ _ _ _
  have hLz : ∀ a k, InRanges a k L → Outside a k (cw sp) := by
    intro a k hin
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hWf : MemFrame M (zcW M sp zzc zzp yi k) (cw sp) := by
    simp only [zcW]
    repeat' first
      | exact MemFrame.refl _ _
      | apply MemFrame.writeLE_inRanges
      | (simp only [InRanges, cw, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
         omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [rd 0x168 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r168
  · rw [rd 0x138 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 0x88 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r88
  · rw [rd 0x390 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r390
  · rw [rd 0x370 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 0x118 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 0x120 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 0x398 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r398
  · rw [rd 0x140 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [w]; omega
  · rw [rd 0x3a8 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r3a8
  · rw [rd 0xd8 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact rd8
  · rw [rd 0x3b0 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r3b0
  · rw [rd 0x3b8 (by omega) (by omega)]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact r3b8
  · exact mf_chain (M := M) (W := cw sp) hWf hF1
      (fun a k ho => by
        simp only [cw, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨ho.1.2, ⟨ho.1.1, by omega, by omega⟩, ho.2⟩)
  · exact lf_chain (M := M) (W := cw sp) hWf hLz hL1
  · rw [FvModexp.Expmc.readLE_of_copied hC1]; simp only [zcW]
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hvd

end FvModexp.Amd64.W4Pro
