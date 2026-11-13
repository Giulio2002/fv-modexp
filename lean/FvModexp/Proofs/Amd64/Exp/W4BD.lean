import FvModexp.Proofs.Amd64.Exp.W4CF

set_option autoImplicit false

/-!
# window-4 (amd64): small frame helpers for the loop-body segments (agent expmc s45)

`Mem.swap`; `Mem.wr` (a write into the loop's written frame slots keeps `Mem`); `FL.slot` (a frame slot outside the
written slots reads as at the anchor); `Mem.mono` helpers used by every body segment `W4S1` … `W4S5`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Loop

theorem Mem.swap {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp : Nat} {M0 M : Memory} {zp zc zzp zzc : Nat}
    (h : Mem R b L g sp M0 M zp zc zzp zzc) : Mem R b L g sp M0 M zzp zzc zp zc :=
  ⟨FL.swap h.1, h.2.1, h.2.2⟩

/-- a write into one of the loop's written frame ranges `fw sp` keeps `Mem` -/
theorem Mem.wr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g fs sp : Nat} {M0 M : Memory} {zp zc zzp zzc : Nat}
    (h : Mem R b L g sp M0 M zp zc zzp zzc) (he : Env R L g fs sp M0) {a : Nat} (v : Nat)
    (hw : (sp - 4296 ≤ a ∧ a + 8 ≤ sp + 0x60) ∨ (sp + 0x98 ≤ a ∧ a + 8 ≤ sp + 0xb8) ∨
      (sp + 0xe0 ≤ a ∧ a + 8 ≤ sp + 0xf0) ∨ (sp + 0x110 ≤ a ∧ a + 8 ≤ sp + 0x118) ∨
      (sp + 0x138 ≤ a ∧ a + 8 ≤ sp + 0x148) ∨ (sp + 0x188 ≤ a ∧ a + 8 ≤ sp + 0x190) ∨
      (sp + 0x358 ≤ a ∧ a + 8 ≤ sp + 0x360) ∨ (sp + 0x370 ≤ a ∧ a + 8 ≤ sp + 0x378)) :
    Mem R b L g sp M0 (M.writeLE a 8 v) zp zc zzp zzc := by
  have hs : 4296 ≤ sp := he.2.1
  have hLs := he.2.2.2.2.2.2.2.2.2.2.1
  have hrt : Outside a 8 R.rt := he.2.2.2.2.2.2.2.1.of_sub (by omega) (by omega)
  refine ⟨FL.write h.1 hLs v ?_ hs, FvModexp.Expmc.inv_writeLE (Or.inr hrt) h.2.1,
    by rw [Arm64.Memory.regions_writeLE]; exact h.2.2⟩
  simp only [fw, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  omega

/-- a frame slot outside the written ranges reads as at the anchor -/
theorem FL.slot {R : RtInv} {L : List (Nat × Nat)} {g fs sp n : Nat} {M0 M : Memory} {zp zc zzp zzc : Nat}
    (h : FL R L sp zp zc zzp zzc M0 M) (he : Env R L g fs sp M0) (hz : Buf R L g fs sp n M0 zp zc)
    (hzz : Buf R L g fs sp n M0 zzp zzc) {a : Nat} (h1 : sp - 4296 ≤ a) (h2 : a + 8 ≤ sp + 0x3c0)
    (hw : Outside a 8 (fw sp)) : M.readLE a 8 = M0.readLE a 8 := by
  have hrt : Outside a 8 R.rt := he.2.2.2.2.2.2.2.1.of_sub h1 (by omega)
  have u1 := hz.2.2.2.2.2.1; have u2 := hzz.2.2.2.2.2.1
  unfold Apart at u1 u2
  refine h.1.readLE _ _ ?_
  simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true] at hw ⊢
  exact ⟨⟨hrt, hw⟩, by omega, by omega⟩

/-- the static frame slots (`m`, `len m`, `cap m`, `k0`) at a loop state -/
theorem Static.rd {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {M0 M : Memory} {zp zc zzp zzc : Nat} (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    (h : FL R L sp zp zc zzp zzc M0 M) (hz : Buf R L g fs sp n M0 zp zc) (hzz : Buf R L g fs sp n M0 zzp zzc) :
    M.readLE (sp + 0x3a8) 8 = mp ∧ M.readLE (sp + 0x3b0) 8 = n ∧ M.readLE (sp + 0x3b8) 8 = mc ∧
      M.readLE (sp + 0xd8) 8 = k0 ∧ M.readLE (sp + 0x390) 8 = yp ∧ M.readLE (sp + 0x398) 8 = ylen := by
  have he := hst.1; have hs : 4296 ≤ sp := he.2.1; have hs2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FL.slot h he hz hzz (by omega) (by omega) (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]
    exact hst.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [FL.slot h he hz hzz (by omega) (by omega) (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]
    exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [FL.slot h he hz hzz (by omega) (by omega) (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]
    exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [FL.slot h he hz hzz (by omega) (by omega) (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]
    exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [FL.slot h he hz hzz (by omega) (by omega) (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]
    exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [FL.slot h he hz hzz (by omega) (by omega) (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]
    exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end FvModexp.Amd64.W4Loop
