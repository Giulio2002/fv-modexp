import FvModexp.Proofs.Amd64.Exp.W2Defs
import FvModexp.Proofs.Common.Conv
import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `z = z.make(2n)`, `zz = zz.make(2n)` — shared definitions (agent expmc s48)

Twin of `Arm64.W2Zm`'s `ZPost`. Each `x.make(2n)` (nat.go:58-69) reuses `x` when `2n ≤ cap x`, else calls
`makeslice(Word, 2n, 2n+4)` (fresh, held in `R.rt`, apart from `L`). `Env.frame` transports the loop environment
along a call's frame (the new live range lies in `R.rt`, hence apart from the frame).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf)

/-- `type:big.Word` -/
@[reducible] def wT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

theorem out_inR {a n p k : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hin : InRanges p k rs) :
    a + n ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem h hr
  omega

/-- the loop environment along a frame that only touches `R.rt` and words apart from the TLS / guard words,
  with the live set extended by fresh `R.rt` ranges -/
theorem Env.frame {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (h : Env R L g fs sp M) (hf : MemFrame M M' (R.rt ++ ws)) (hg : Outside (g + 16) 8 ws)
    (hfs : Outside (fs - 8) 8 ws) (hx : LiveExt R L L') : Env R L' g fs sp M' := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := h
  have hgr : M'.readLE (g + 16) 8 = M.readLE (g + 16) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨hgrt, hg⟩)
  have hfr : M'.readLE (fs - 8) 8 = M.readLE (fs - 8) 8 :=
    hf.readLE _ _ (by simp only [outside_append]; exact ⟨hfrt, hfs⟩)
  obtain ⟨ns, rfl, hns, -⟩ := hx
  refine ⟨hal, hsp1, hsp2, by rw [hf.accessible]; exact hacc, hg1, by rw [hf.accessible]; exact hg2,
    by rw [hgr]; exact hg3, hrt, hga, hgrt, ?_, hfs1, by rw [hf.accessible]; exact hfacc, by rw [hfr]; exact hfrd,
    hfw, hfrt, by rw [hf.accessible]; exact hadx⟩
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hLs r hr
  · have := out_inR hrt (hns r hr).1
    simp only [outside_cons, outside_nil, and_true]; omega

/-- the facts about a buffer after `x.make(2n)` (reuse or fresh `makeslice`) -/
@[reducible] def ZPost (R : RtInv) (L L' : List (Nat × Nat)) (b b' g fs sp n : Nat) (M M' : Memory)
    (ws : List (Nat × Nat)) (zp zc zp' zc' : Nat) : Prop :=
  Env R L' g fs sp M' ∧ Buf R L' g fs sp n M' zp' zc' ∧ zp' % 8 = 0 ∧ LiveExt R L L' ∧
  b - blockSize (8 * (2 * n + 4)) true ≤ b' ∧
  MemFrame M M' (R.rt ++ ws) ∧ LiveFrame M M' L [] ∧
  R.inv b' L' g (view R.rt L' M') ∧ M'.regions = M.regions ∧
  ((zp' = zp ∧ zc' = zc ∧ L' = L ∧ b' = b) ∨ (InRanges zp' (8 * zc') R.rt ∧ ApartAll zp' (8 * zc') L))

theorem out_of_in {a k lo len : Nat} (h : Apart a k lo len) :
    ∀ (ws : List (Nat × Nat)), (∀ q ∈ ws, lo ≤ q.1 ∧ q.2 ≤ lo + len) → Outside a k ws
  | [], _ => trivial
  | q :: ws, hq => by
    have h1 := hq q (by simp)
    refine ⟨by unfold Apart at h; omega, out_of_in h ws (fun q' hq' => hq q' (by simp [hq']))⟩

/-- the words `zz.make` may write besides `R.rt`: the makeslice callee window, the `2n+4` spill, `z`'s spills -/
@[reducible] def zw2 (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4296, sp + 0x18), (sp + 0x80, sp + 0x90), (sp + 0x170, sp + 0x178)]

/-- the words `z.make` may write besides `R.rt`: the makeslice callee window and the `2n+4` spill -/
@[reducible] def zw1 (sp : Nat) : List (Nat × Nat) := [(sp - 4296, sp + 0x18), (sp + 0x88, sp + 0x90)]

theorem zw1_in (sp : Nat) : ∀ q ∈ zw1 sp, sp - 4296 ≤ q.1 ∧ q.2 ≤ sp - 4296 + (4296 + 0x2a8) := by
  intro q hq; simp only [zw1, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> simp only <;> omega

theorem zw2_in (sp : Nat) : ∀ q ∈ zw2 sp, sp - 4296 ≤ q.1 ∧ q.2 ≤ sp - 4296 + (4296 + 0x2a8) := by
  intro q hq; simp only [zw2, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp only <;> omega

set_option maxRecDepth 20000 in
/-- the post of a `makeslice(Word, 2n, 2n+4)` path, from the contract's post (small context); `Mw` = the memory at
  the call with the spills `ws0` written (inside the frame) -/
theorem fresh_post {R : RtInv} {L : List (Nat × Nat)} {b g fs sp n zp zc p r : Nat} {M Mw m : Memory}
    {ws zw : List (Nat × Nat)} (hzw0 : (sp - 4296, sp + 0x18) ∈ zw)
    (hzwi : ∀ q ∈ zw, sp - 4296 ≤ q.1 ∧ q.2 ≤ sp - 4296 + (4296 + 0x2a8))
    (he : Env R L g fs sp M) (hn16 : n ≤ 2 ^ 16)
    (hw : MemFrame M Mw ws) (hLw : LiveFrame M Mw L [])
    (hwz : ∀ a k, Outside a k zw → Outside a k ws)
    (hLF : LiveFrame Mw m L []) (hrg : m.regions = M.regions)
    (hMF : MemFrame Mw m (R.rt ++ [(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)]))
    (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) (hle : p + r ≤ 2 ^ 48)
    (hacc : M.accessible p r true = true) (h8 : p % 8 = 0) (hsz : 8 * (2 * n + 4) ≤ r)
    (hr : r = blockSize (8 * (2 * n + 4)) true)
    (hinv : R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)) :
    ZPost R L (L ++ [(p, p + r)]) b (b - r) g fs sp n M m zw zp zc p (2 * n + 4) := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hF : MemFrame M m (R.rt ++ zw) := by
    refine hw.trans hMF (fun a k ho => ⟨hwz a k (by simp only [outside_append] at ho; exact ho.2), ?_⟩)
    have hro : Outside a k R.rt := by simp only [outside_append] at ho; exact ho.1
    have h0 := MemFrame.outside_mem (by simp only [outside_append] at ho; exact ho.2) hzw0
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hro, by simp only at h0; omega, by simp only at h0; omega⟩
  have hgo : Outside (g + 16) 8 zw := out_of_in hgw zw hzwi
  have hfo : Outside (fs - 8) 8 zw := out_of_in hfw zw hzwi
  have hx : LiveExt R L (L ++ [(p, p + r)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have he' := Env.frame he hF hgo hfo hx
  have hpw := out_inR hwrt hIn
  have hpg := out_inR hgrt hIn
  have hpf := out_inR hfrt hIn
  have hacc' : m.accessible p (8 * (2 * n + 4)) true = true := by
    rw [hF.accessible]; exact Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
  refine ⟨he', ⟨by omega, by omega, hacc', by omega, Or.inl ⟨(p, p + r), by simp, by omega, by simp only; omega⟩,
      by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩, h8,
    hx, by omega, hF, hLw.trans hLF (fun _ _ h => h), hinv, hrg, Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), ?_⟩⟩
  intro q hq; have := hAp q hq; unfold Apart at this ⊢; omega

end FvModexp.Amd64.W2Pro
