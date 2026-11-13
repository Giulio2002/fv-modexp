import FvModexp.Proofs.Amd64.NatQ.DrsFMulQ
import FvModexp.Proofs.Amd64.NatQ.DrsB4D

set_option autoImplicit false

/-! (amd64 twin (asm s52) of the definitions in Arm64/NatQ/DrsF4C.lean; adapted from Amd64/NatQ/DrsB4D.lean)
# `divRecursiveStep` (amd64), final block segment 4: definitions for the call of `nat.mul` (natdiv.go:867)

* `rF4`/`raF4`: the return site `0x5f0319` (= `seg45 + 0xa99`) is admissible for `nat.mul`'s program `ns`.
* `AF3.own`: `AF3` survives the own stores `is4` (return slot and the stack arguments `r-400 … r-376`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the return address of the final block's product (`CALL 0x5f0314`) -/
abbrev rF4 : Nat := 0x5f0319

set_option maxRecDepth 20000 in
/-- the return site `0x5f0319` (after `CALL nat.mul`) is admissible for `nat.mul`'s program -/
theorem raF4 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (ns : List String)
    (hns : ns.contains DivLarge.drsFn = false) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) rF4 := by
  have := drsN_retAddr_restrict hap (cs := Extracted.seg45) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg45.name = DivLarge.drsFn from rfl]; exact hns) 0xa99 (by decide) (by decide)
  rw [show Extracted.seg45.base = 0x5ef880 from rfl] at this
  exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`AF3` across the own stores `is4`** (state `S` with the new memory `M'`) -/
theorem AF3.own {R : RtInv} {c : Cx} {s S : State} {Lk : List (Nat × Nat)} {bk j : Nat} {Z U : List Nat}
    {qn : Nat} (hA : AF3 R c s Lk bk S j Z U qn) (M' : Memory) (hF4 : MemFrame S.mem M' (is4 s))
    (hreg : M'.regions = S.mem.regions) :
    AF3 R c s Lk bk { S with mem := M' } j Z U qn := by
  have hcr := hA.cr
  have hev := hA.ev
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hu1 := hcr.u1ul
  have h0' : 408 ≤ (s.regs 4).toNat := by omega
  have hF : MemFrame S.mem M' (fw s) := hF4.mono fun x n ho => by
    simp only [fw, win, is4, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF4.readLE _ _ (by simp only [win, is4, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hsto : Outside c.st 24 (win s c.W 96) := hpre.sti.2.1
  have eW : stW M' c.st = stW S.mem c.st := rd _ _ (hsto.of_sub (by omega) (by omega))
  have eL : stLen M' c.st = stLen S.mem c.st := rd _ _ (hsto.of_sub (by omega) (by omega))
  have eC : stCap M' c.st = stCap S.mem c.st := rd _ _ (hsto.of_sub (by omega) (by omega))
  have eqv : c.qv s M' = c.qv s S.mem := by simp only [Cx.qv]; rw [eW]
  have ft : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => rd _ _ (hcr.t0w.of_sub h1 h2)
  have fu : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = S.mem.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hrgw := hA.rg.w
  have fz : M'.readLE (c.qv s S.mem) (8 * (3 * c.vl)) = S.mem.readLE (c.qv s S.mem) (8 * (3 * c.vl)) := rd _ _ hrgw
  have hio : FOut s (is4 s) := by simp only [FOut, is4, outside_cons, outside_nil, and_true]; omega
  have hfo : FixOut s (is4 s) := by simp only [FixOut, is4, outside_cons, outside_nil, and_true]; omega
  have hhi : HiOut s (is4 s) := by simp only [HiOut, is4, outside_cons, outside_nil, and_true]; omega
  have hlen := hA.fp.len
  have hqle := hA.qle
  refine ⟨hA.pc, hA.sp, hA.r5, hA.r14, hA.fs, hA.df, hA.x15, hcr, Ev.own hcr hev hF hreg, Fp.own hcr hA.fp hF,
    hA.bd.frame hF4 hfo hio (rd _ _ hvw) (fu _ _ (by omega) (by omega)) (rd _ _ hqw), hA.jB, hA.li,
    by rw [limbs_congr (ft _ _ (Nat.le_refl _) (Nat.le_refl _))]; exact hA.qk,
    by rw [limbs_congr (fu _ _ (Nat.le_refl _) (by omega))]; exact hA.uk, hqle, ?qv, ?qN,
    hA.q3.frame hF4 hhi h0', by rw [eqv]; exact hA.v3.frame hF4 hhi h0', by rw [eqv]; exact hA.rg,
    FL.hdr hA.fl eW eC, by rw [eqv, fz]; exact hA.z0, ?bud⟩
  case qv =>
    show M'.readLE c.t0 (8 * qn) = M'.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [ft _ _ (Nat.le_refl _) (by omega), ft _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hA.qv
  case qN =>
    rcases hA.qN with h | h
    · exact Or.inl h
    · right; rw [ft _ _ (by omega) (by omega)]; exact h
  case bud => exact bud_cap eC hA.bud

end FvModexp.Amd64.Q.DivRec
