import FvModexp.Proofs.Amd64.Exp.P2DEnt
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.ExpBase
import FvModexp.Proofs.Common.GenReg

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): the window dispatch and call (odd `x`, `logM ≥ 2`, nat.go:960-966) (agent asm s68;
amd64 twin of infra's arm64 `P2DWinR`)

`winR`: from `oddE` (`0x5e902d`): `logM < 48` → window 2; else `bitLen y = 64 (len y - 1) + bitLen(top)` (smear +
`BSRQ`; `smearR` copied from agent expmc's `Amd64.W2Pro.smearR`) `< 48` → window 2, else window 4. Both branches store
`y` (`[sp] := yp`, `[sp + 8] := len y`, `[sp + 0x10] := [sp + 0x88]` = `cap y`) and `CALL` (return `w2R` / `w4R`):
the exits are the window entries (`w2E`, `w4E`) with `RSP = sp - 8`, every argument register, `RBP`, `R14`, FS base,
`X15`, DF kept and memory `Mw`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

abbrev w2E : Nat := 6200864
abbrev w4E : Nat := 6197952
abbrev w2R : Nat := 0x5e90da
abbrev w4R : Nat := 0x5e90b9

/-- the memory at a window entry -/
@[reducible] def Mw (M : Memory) (sp yp yl r : Nat) : Memory :=
  (((M.writeLE sp 8 yp).writeLE (sp + 8) 8 yl).writeLE (sp + 16) 8 (M.readLE (sp + 0x88) 8)).writeLE (sp - 8) 8 r

/-- the smear chain as the amd64 code computes it (copied from agent expmc's `Amd64.W2Pro.smearR`, W2ZcDefs) -/
def smearR (x : BitVec 64) : BitVec 64 :=
  let a := x >>> 1 ||| x
  let b := a >>> 2 ||| a
  let c := b >>> 4 ||| b
  let d := c >>> 8 ||| c
  let e := d >>> 16 ||| d
  e >>> 32 ||| e

theorem or_c (a b : BitVec 64) : (a ||| b) = (b ||| a) := BitVec.or_comm a b

theorem smearR_eq (x : BitVec 64) : smearR x = BitLenA64.smearBV x := by
  unfold smearR BitLenA64.smearBV
  simp only [or_c (x >>> 1) x, or_c ((x ||| x >>> 1) >>> 2)]
  generalize ha : (x ||| x >>> 1 ||| (x ||| x >>> 1) >>> 2) = a
  simp only [or_c (a >>> 4) a]
  generalize hb : (a ||| a >>> 4) = b
  simp only [or_c (b >>> 8) b]
  generalize hc : (b ||| b >>> 8) = c
  simp only [or_c (c >>> 16) c]
  generalize hd : (c ||| c >>> 16) = d
  simp only [or_c (d >>> 32) d]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem winR {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp yp yl lm w : Nat) (M : Memory)
    (hyl0 : 1 ≤ yl) (hyl : yl ≤ 2 ^ 20) (hlm : lm ≤ 2 ^ 13) (hyp : yp + 8 * yl ≤ 2 ^ 48)
    (hya : M.accessible (yp + 8 * (yl - 1)) 8 false = true) (hw : M.readLE (yp + 8 * (yl - 1)) 8 = w) (hw0 : w ≠ 0)
    (hsp : 8 ≤ sp) (hsp2 : sp + 0x90 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 0x20 true = true)
    (hacc2 : M.accessible (sp + 0x88) 8 false = true)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 oddE) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (h11 : S.regs 11 = BitVec.ofNat 64 yp) (h2 : S.regs 2 = BitVec.ofNat 64 yl)
    (h10 : S.regs 10 = BitVec.ofNat 64 lm) (hmem : S.mem = M)
    (K : ∀ (c : Nat), (c = w2E ∧ (lm < 48 ∨ 64 * (yl - 1) + Aux.bitLen w < 48) ∨
        c = w4E ∧ 48 ≤ lm ∧ 48 ≤ 64 * (yl - 1) + Aux.bitLen w) → ∀ S' : State, S'.rip = BitVec.ofNat 64 c →
      S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = S.regs 0 → S'.regs 3 = S.regs 3 → S'.regs 1 = S.regs 1 → S'.regs 7 = S.regs 7 →
      S'.regs 6 = S.regs 6 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 →
      S'.df = S.df → S'.mem = Mw M sp yp yl (if c = w2E then w2R else w4R) →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have ry : M.readLE (yp + yl * 8 - 8) 8 = w := by rw [← hw, show yp + yl * 8 - 8 = yp + 8 * (yl - 1) by omega]
  have hw64 : w < 2 ^ 64 := by rw [← hw]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  subst hmem
  have e8 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have esh : (BitVec.ofNat 64 yl - 1#64) <<< 6 = BitVec.ofNat 64 (64 * (yl - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  janus64_run [ry, e8] until [w2E, 6197375]
  · exact K w2E (Or.inl ⟨rfl, Or.inl hbr⟩) _ rfl (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) rfl rfl rfl rfl
  gen_reg 13 as t with hT
  have hts : t = BitLenA64.smearBV (BitVec.ofNat 64 w) := by rw [← hT, ← smearR_eq]; rfl
  have ht0 : t.toNat ≠ 0 := by
    rw [hts]; exact (BitLenA64.smearBV_log2 _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw64]; omega)).1
  have ht0' : (t.toNat = 0) = False := by simp [ht0]
  have hbs : BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 t.toNat) = BitVec.ofNat 64 (Aux.bitLen w - 1) := by
    rw [hts, BitLenA64.clz_smear, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw64]
    have hc := Util.clz_bl 64 w hw64
    congr 1; omega
  have hb1 : 1 ≤ Aux.bitLen w := by
    have := Exp.bitLen_pos (show 0 < w by omega); exact this
  have hb64 : Aux.bitLen w ≤ 64 := by have := Util.clz_bl 64 w hw64; omega
  have eR : BitVec.ofNat 64 (Aux.bitLen w - 1) + BitVec.ofNat 64 (64 * (yl - 1) + 1) =
      BitVec.ofNat 64 (64 * (yl - 1) + Aux.bitLen w) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hti : (BitVec.ofNat 64 (64 * (yl - 1) + Aux.bitLen w)).toInt = ((64 * (yl - 1) + Aux.bitLen w : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; split <;> omega
  janus64_run [ht0, ht0', hbs, esh, eR, hti, ry, e8] until [w2E, w4E]
  · exact K w2E (Or.inl ⟨rfl, Or.inr (by omega)⟩) _ rfl (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) rfl rfl rfl rfl
  · exact K w4E (Or.inr ⟨rfl, by omega, by omega⟩) _ rfl (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
      (by janus64_simp) (by janus64_simp) rfl rfl rfl rfl

end FvModexp.Amd64.P2D
