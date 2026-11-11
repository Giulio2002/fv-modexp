import FvModexp.Proofs.Common.StackScr

/-!
# The `*stack` object across code that does not use it (agent infra)

A function that passes `stk` on but whose own writes avoid the header keeps `StkOK`, and its post can state
`StackBack` with the old array (`stkOK_frame`, `stackBack_frame`).
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Contracts

/-- `StkOK` survives a step whose memory frame keeps the three header words -/
theorem stkOK_hdr {m m' : Memory} {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {rs : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' rs) (e0 : stW m' st = stW m st) (e1 : stLen m' st = stLen m st)
    (e2 : stCap m' st = stCap m st) (hLE : LiveExt R L L') : StkOK m' R L' st := by
  obtain ⟨h8, hh, hacc, h48, hlive, hlc, hc40⟩ := h
  refine ⟨h8, hLE.held hh, by rw [hF.accessible]; exact hacc, h48, ?_, by rw [e1, e2]; exact hlc,
    by rw [e2]; exact hc40⟩
  rw [e0, e2]
  intro hc
  obtain ⟨a1, a2, a3, a4⟩ := hlive hc
  exact ⟨a1, hLE.held a2, by rw [hF.accessible]; exact a3, a4⟩

/-- `StackBack` with the old array, from the three header words -/
theorem stackBack_hdr {m m' : Memory} {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {rs : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' rs) (e0 : stW m' st = stW m st) (e1 : stLen m' st = stLen m st)
    (e2 : stCap m' st = stCap m st) (hLE : LiveExt R L L') : StackBack R L L' st m m' :=
  ⟨stkOK_hdr h hF e0 e1 e2 hLE, e1, Or.inl ⟨e0, e2⟩⟩

theorem stkOK_frame {m m' : Memory} {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {rs : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' rs) (ho : Outside st 24 rs) (hLE : LiveExt R L L') :
    StkOK m' R L' st ∧ stW m' st = stW m st ∧ stLen m' st = stLen m st ∧ stCap m' st = stCap m st := by
  have e0 : stW m' st = stW m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have e1 : stLen m' st = stLen m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have e2 : stCap m' st = stCap m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  exact ⟨stkOK_hdr h hF e0 e1 e2 hLE, e0, e1, e2⟩

theorem stackBack_frame {m m' : Memory} {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {rs : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' rs) (ho : Outside st 24 rs) (hLE : LiveExt R L L') :
    StackBack R L L' st m m' := by
  obtain ⟨h1, e0, e1, e2⟩ := stkOK_frame h hF ho hLE
  exact ⟨h1, e1, Or.inl ⟨e0, e2⟩⟩

end FvModexp
