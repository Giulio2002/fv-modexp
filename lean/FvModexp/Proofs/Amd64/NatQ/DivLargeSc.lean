import FvModexp.Proofs.Amd64.NatQ.DivLargeCpB
import FvModexp.Proofs.Amd64.NatQ.DivLargeShB
import FvModexp.Proofs.Amd64.NatQ.DivLargeShC

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeSc.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): the scaling (natdiv.go:609-616), `joinU` → the alias test

`shift = 0`: `copy(v, vIn)`, `copy(u, uIn)`, `u[il] = 0` (`cpA`, `cpB`); `shift ≠ 0`: `lshVU(v, vIn, shift)`,
`lshVU(u, uIn, shift)`, `u[il] = carry` (`shA`, `shB`, `shC`). `Mem.grd`: the stack guard word is unchanged after
`stk.nat` (port of the arm64 lemma).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

/-- the stack guard word is unchanged after `stk.nat` (pure) -/
theorem Mem.grd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat}
    {M : Janus.Arm64.Memory} (hM : Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk M) :
    M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
  have hga := hE.pre.ce.2.2.2.2.2.1; have hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.2.1
  unfold Apart at hga
  have hk : Outside ((s.regs 14).toNat + 16) 8 (stkWs s.mem st) :=
    outside_stkWs hE.pre (hE.pre.sti.2.2.1.symm) fun hc => (hE.pre.sti.2.2.2 hc).2.symm
  refine hM.fr.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨⟨hgr, ?_⟩, g_wsL hE⟩, hk⟩
  simp only [win, outside_cons, outside_nil, and_true]; omega

theorem scale (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C S) (Q : State → Prop)
    (k : ∀ sh T, AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hgrd := Mem.grd hE hS.mem
  by_cases hclz : Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0
  · exact cpA impl R hmv b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C hE S hS hgrd hclz Q
      fun V hV => cpB impl R hmv b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C hE V hV hclz Q (k 0)
  · exact shA impl hap R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C hE S hS hgrd _ rfl hclz Q
      fun T1 h1 => shB impl hap R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C _ hE T1 h1 Q
        fun T2 h2 => shC impl R b L c zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C _ hE T2 h2 Q (k _)

end FvModexp.Amd64.Q.DivLarge
