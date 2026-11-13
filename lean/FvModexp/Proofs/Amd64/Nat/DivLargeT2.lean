import FvModexp.Proofs.Amd64.Nat.DivLargeTP
import FvModexp.Proofs.Amd64.Nat.DivLargeCallees

set_option autoImplicit false

/-!
# `divLarge` (amd64): the tail, part 2 (natdiv.go:638-641): `r = u.norm()`, the deferred `stk.restore`, the return

`rJoin` (`+0x716`): `AX = u.ptr` (`RSP - 104`), `DI = len u` (`RSP - 200`) → `u.norm()` (`rnorm`); exit `+0x737`:
`CX = cap u` (`RSP - 184`), `CMPQ DI, CX; JA panic`; `r` stored (`RSP - 88 … - 72`); defer bit cleared (`RSP - 209`);
`DX = [RSP - 16] = RSP - 40` (the defer record), `CALL [DX]` (`nat.divLarge.deferwrap1`, `dsum`, return `+0x76f`);
results `RAX, RBX, RCX = q`, `RDI, RSI, R8 = r`; `ADDQ $0x128, SP; POPQ BP; RET`. Port of `Arm64/Nat/DivLargeT2.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `u.norm()`'s exit (`RDI = rl`): `r` stored, the deferred closure, the return -/
theorem t2c (impl : List Amd64.Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 ql : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {T : State}
    (hT : AtR R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T)
    {rl : Nat} (hrl : rl ≤ il + 1) (hrv : natVal T.mem P rl = natVal s.mem ip il % natVal s.mem vp vl)
    (hrn : NatNorm T.mem P rl) (X : State) (hpc : X.rip = BitVec.ofNat 64 rExit) (hm : X.mem = T.mem)
    (h0 : X.regs 0 = BitVec.ofNat 64 P) (h7 : X.regs 7 = BitVec.ofNat 64 rl) (hsp : X.regs 4 = s.regs 4 - 304#64)
    (h5 : X.regs 5 = s.regs 4 - 8#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hx15 : X.xmm 15 = 0#128) (hdf : X.df = false) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) X (RQ R b L c zp zc st up uc ip il vp vl s) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hsw := hl.sw
  have hpre := hE.pre
  have hMU := hT.mem
  have hM := hMU.mem
  have hU := hT.ua; have hQ := hT.qa
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48; have hq40 := hQ.c40; have hq48 := hQ.p48
  have hqcap := hQ.cap; have hql := hT.qle
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  have hTacc : ∀ a n v, T.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : T.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by rw [hTacc]; exact hw
  have hsacc : T.mem.accessible st 24 true = true := by rw [hTacc]; exact hpre.sti.1.2.2.1
  have m1 := hM.ra; have m2 := hM.bp; have mdp := hM.dp
  have mdf : T.mem.readLE ((s.regs 4).toNat - 40) 8 = 6222240 := hM.dfn
  have mcap := hM.hcap; have mC := hMU.sC; have mq0 := hT.sq0; have mq1 := hT.sq1; have mq2 := hT.sq2
  have f8 : T.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 = st := by
    rw [show (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 by omega]; exact hM.dst
  have f16 : T.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 = stLen s.mem st := by
    rw [show (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 by omega]; exact hM.dn
  have hc2 := hT.c2len
  have hst48 := hl.st48
  have hra := hE.ra
  have hD : Summary (LibDivL.program.link impl) 6222240 Restore.Pre Restore.Post := dsum impl
  have hx0 := hE.x15; have hdf0 := hE.df0
  janus64_run [m1, m2, mdp, mdf, mcap, mC, mq0, mq1, mq2, f8, f16, hfs] calls [hD]
  rename_i _ _ h5C h14C hx15C hfsC hdfC hlen hFF
  have hFE : MemFrame T.mem (((((T.mem.writeLE ((s.regs 4).toNat - 88) 8 P).writeLE ((s.regs 4).toNat - 80) 8 rl).writeLE
      ((s.regs 4).toNat - 72) 8 C).writeLE ((s.regs 4).toNat - 209) 1 0).writeLE ((s.regs 4).toNat - 312) 8 6221967)
      [((s.regs 4).toNat - 88, (s.regs 4).toNat - 64), ((s.regs 4).toNat - 209, (s.regs 4).toNat - 208),
        ((s.regs 4).toNat - 312, (s.regs 4).toNat - 304)] := by janus_frame
  have hW : MemFrame T.mem _ (finW s st) := (mfTrans hFE hFF).mono fun a n ho => by
    simp only [finW, outside_cons, outside_nil, and_true] at ho
    simp only [outside_append, outside_cons, outside_nil, and_true]; omega
  simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] at h5C h14C
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lpost hE hT hrl hrv hrn hW hlen _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals first
    | exact h5C.trans h14
    | (rw [h14C, h14])
    | (rw [hx15C, hx15, hx0])
    | (rw [hfsC])
    | exact hdf0.symm
    | (rw [hdfC, hdf0])
    | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the tail, part 2**: `AtR` → `r = u.norm()` → `r` stored → `stk.restore` → return (`RQ`) -/
theorem t2 (impl : List Amd64.Segment) (R : RtInv)
    {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 ql : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (T : State)
    (hT : AtR R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) T (RQ R b L c zp zc st up uc ip il vp vl s) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hT.ua
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have m0 := hT.mem.sP; have m1 := hT.mem.sL
  obtain ⟨-, ⟨-, -, hw⟩, -, -⟩ := hE.pre.ce
  have hwacc : T.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    rw [hT.mem.mem.fr.accessible]; exact hw
  have hpc := hT.pc; have hsp := hT.sp; have h5 := hT.r5; have h14 := hT.r14; have hfs := hT.fs
  have hx15 := hT.x15; have hdf := hT.df
  janus64_run [m0, m1] until [rHead]
  refine rnorm impl (retAddrOf s) T.mem P (il + 1) (natVal s.mem ip il % natVal s.mem vp vl) (s.regs 4 - 304#64)
    (s.regs 4 - 8#64) (s.regs 14) s.fsBase 0#128 _
    (fun s' n' hpc' hm' h0' h7' hsp' h5' h14' hfs' hx15' hdf' hle hv hn =>
      t2c impl R hE hT hle hv hn s' hpc' hm' h0' h7' hsp' h5' h14' hfs' hx15' hdf')
    (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hU.pacc (Nat.le_refl _) (by omega)))
    (il + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hT.rval
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hx15 | exact hdf | rfl

end FvModexp.Amd64.DivLarge
