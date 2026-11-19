import FvModexp.Proofs.Amd64.Exp.W2FunP
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# `PreD` survives installing the return address (amd64, Janus v0.4.0 `hinv` of `ExpW2.ens`; top s53)

`janus64_pre_setRet` over the whole `PreD` exceeded 5 min (the conditional conjuncts `2·n ≤ zc → …` and `0 < stCap → …` leave
goals that the closer's `omega` fails on in the full context). Case-split on both guards (the pilot's `divpre_setRet` pattern),
one declaration per case; this module only depends on `W2FunP`, so it compiles beside the row's other modules.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpW2

set_option maxHeartbeats 16000000 in
theorem preD_setRet_pp (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {e : Nat} {args : List W64} (hs : CallSetup0 e args s) (hret : RetAddr p ret) (h1 : 2 * n ≤ zc) (h2 : 0 < stCap s.mem st)
    (hp : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s) : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpW2.PreD, FvModexp.Amd64.ExpW2.EPreA, FvModexp.natVal, FvModexp.stLen, FvModexp.Amd64.W2En.EEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.W2En.wTy, FvModexp.Amd64.MontHyp.hasADX, FvModexp.Amd64.W2En.OE, FvModexp.Amd64.RunIface.gA, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.W2En.free, FvModexp.Amd64.CallW.CEnv, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.natNorm_setRet, FvModexp.Amd64.readLE_setRet_or_zero, h1, h2, false_implies, true_implies]

set_option maxHeartbeats 16000000 in
theorem preD_setRet_pn (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {e : Nat} {args : List W64} (hs : CallSetup0 e args s) (hret : RetAddr p ret) (h1 : 2 * n ≤ zc) (h2 : ¬ 0 < stCap s.mem st)
    (hp : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s) : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpW2.PreD, FvModexp.Amd64.ExpW2.EPreA, FvModexp.natVal, FvModexp.stLen, FvModexp.Amd64.W2En.EEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.W2En.wTy, FvModexp.Amd64.MontHyp.hasADX, FvModexp.Amd64.W2En.OE, FvModexp.Amd64.RunIface.gA, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.W2En.free, FvModexp.Amd64.CallW.CEnv, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.natNorm_setRet, FvModexp.Amd64.readLE_setRet_or_zero, h1, h2, false_implies, true_implies]

set_option maxHeartbeats 16000000 in
theorem preD_setRet_np (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {e : Nat} {args : List W64} (hs : CallSetup0 e args s) (hret : RetAddr p ret) (h1 : ¬ 2 * n ≤ zc) (h2 : 0 < stCap s.mem st)
    (hp : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s) : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpW2.PreD, FvModexp.Amd64.ExpW2.EPreA, FvModexp.natVal, FvModexp.stLen, FvModexp.Amd64.W2En.EEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.W2En.wTy, FvModexp.Amd64.MontHyp.hasADX, FvModexp.Amd64.W2En.OE, FvModexp.Amd64.RunIface.gA, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.W2En.free, FvModexp.Amd64.CallW.CEnv, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.natNorm_setRet, FvModexp.Amd64.readLE_setRet_or_zero, h1, h2, false_implies, true_implies]

set_option maxHeartbeats 16000000 in
theorem preD_setRet_nn (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {e : Nat} {args : List W64} (hs : CallSetup0 e args s) (hret : RetAddr p ret) (h1 : ¬ 2 * n ≤ zc) (h2 : ¬ 0 < stCap s.mem st)
    (hp : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s) : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc (s.setRet ret) := by
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpW2.PreD, FvModexp.Amd64.ExpW2.EPreA, FvModexp.natVal, FvModexp.stLen, FvModexp.Amd64.W2En.EEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.W2En.wTy, FvModexp.Amd64.MontHyp.hasADX, FvModexp.Amd64.W2En.OE, FvModexp.Amd64.RunIface.gA, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.W2En.free, FvModexp.Amd64.CallW.CEnv, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.natNorm_setRet, FvModexp.Amd64.readLE_setRet_or_zero, h1, h2, false_implies, true_implies]

theorem preD_inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (p : Janus.Amd64.Program) (e : Nat) (args : List W64) :
    Ensures.SetRetInv p e args (PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc) := by
  intro s ret hs hret hp
  by_cases h1 : 2 * n ≤ zc <;> by_cases h2 : 0 < stCap s.mem st
  · exact preD_setRet_pp R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s ret hs hret h1 h2 hp
  · exact preD_setRet_pn R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s ret hs hret h1 h2 hp
  · exact preD_setRet_np R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s ret hs hret h1 h2 hp
  · exact preD_setRet_nn R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s ret hs hret h1 h2 hp

end FvModexp.Amd64.ExpW2
