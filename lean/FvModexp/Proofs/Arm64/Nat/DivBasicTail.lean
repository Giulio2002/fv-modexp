import FvModexp.Proofs.Arm64.Nat.DivBasicTailS
import FvModexp.Proofs.Arm64.Nat.DivBasicTailN
/-!
# `divBasic` (arm64): `ujn = u[j+n-1]`; `if j == m && m == len(q) && qhat == 0 { continue }`; `q[j] = qhat`; `j--`
(natdiv.go:719-722), `+0x2d8 → head`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic


theorem tail (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qh : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S tailPt j)
    (h0 : S.regs 0 = BitVec.ofNat 64 vl) (h4 : S.regs 4 = BitVec.ofNat 64 ul) (h7 : S.regs 7 = BitVec.ofNat 64 up)
    (h2 : S.regs 2 = BitVec.ofNat 64 qh) (hqh : qh < 2 ^ 64) (hj : j + vl ≤ ul)
    (hst : ¬ skipQ j ul vl ql qh → j < ql) (Q : State → Prop)
    (k : ∀ S', Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' (j + 2 ^ 64 - 1)
        (S.mem.readLE (up + 8 * (j + vl - 1)) 8) →
      (∀ a n, S'.mem.readLE a n = (if skipQ j ul vl ql qh then S.mem else S.mem.writeLE (qp + 8 * j) 8 qh).readLE a n) →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  by_cases hsk : skipQ j ul vl ql qh
  · exact tailS impl R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qh hB h0 h4 h7 h2 hqh hj hsk Q k
  · exact tailN impl R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qh hB h0 h4 h7 h2 hqh hj hst hsk Q k

end FvModexp.Arm64.DivBasic
