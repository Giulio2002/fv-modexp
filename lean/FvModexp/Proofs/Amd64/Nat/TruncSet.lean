import FvModexp.Proofs.Amd64.Nat.TruncSetC
import FvModexp.Proofs.Amd64.Nat.TruncMid

/-!
# `nat.trunc` (amd64): the `set` path (`len x < w`, `JB +0x136`), reuse of `z` (`len x ≤ cap z`, `CMPQ CX, SI; JL`
not taken): entry to the join of `z.make(len x)` (`+0x1a2`), then `copyS`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setReuse (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibTrunc.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) (s : State)
    (he : Entry s zp zl zc x xl xc n) (hw : xl < wOf n) (hz : xl ≤ zc) (hz0 : 0 < zc)
    (hpre : Pre R b L zp zl zc x xl n s) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x xl n s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hwa, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, ⟨hz40, -, -⟩, ⟨hx40, -, -, -, -⟩, hx16, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh' := shr_w' n hn20
  have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
  have hxm : xl % 18446744073709551616 = xl := Nat.mod_eq_of_lt (by omega)
  have hzm : zc % 18446744073709551616 = zc := Nat.mod_eq_of_lt (by omega)
  janus64_run [hsh, hsh', hwm, hxm, hzm, BitVec.msb_eq_decide] until [hJoinS]
  refine copyS impl R hmv b L zp zc x xl n s zp zc L b _
    (mid_of_reuse hpre (Nat.le_refl _) hz hz0 hra hx15 hdf ?hF ?_ ?_ (fun h => absurd h (by omega))) hw
    (hpre.2.1.resolve_right (by omega)) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  case hF => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | exact hx15 | exact hdf | skip

end FvModexp.Amd64.Trunc
