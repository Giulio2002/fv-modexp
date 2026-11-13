import FvModexp.Proofs.Amd64.Nat.MulAddWWVww

set_option autoImplicit false

/-!
# `nat.mulAddWW` (amd64): the EXACT write set on the reuse path — the `mulAddVWW.abi0` call and the tail

(agent divmc, amd64 port of Arm64/Nat/MulAddWWXA.lean, wrapping asm's `MulAddWW*` proof.) `XM` adds to `Mid` (the
facts at `+0xae`): the result's capacity `< 2^40` and, when `z` is large enough (`m + 1 ≤ zc`: the reuse path), that
the result array is `z`'s and only `z[0:m+1]` of it was written (memory and live frames over `[zp, zp + 8(m+1))`).
`XM.frame0`: a write to the stack or to `p[0:m+1]` keeps it. `vwwX` / `tailX`: `vww` / `tail` re-run carrying `XM`
to the return, where the extra post `XQ` holds.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.MulAddWW

/-- the extra facts of the exact-write variant -/
structure XM (R : RtInv) (L : List (Nat × Nat)) (zp zc xl : BitVec 64) (s : State) (p c : Nat)
    (M : Janus.Arm64.Memory) : Prop where
  c40 : c < 2 ^ 40
  ex : xl.toNat + 1 ≤ zc.toNat → p = zp.toNat ∧ c = zc.toNat ∧
    MemFrame s.mem M (R.rt ++ win s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * (xl.toNat + 1))]) ∧
    LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * (xl.toNat + 1))]

/-- **the extra post** (amd64 results `AX, BX, CX` = `p', n', c'`): capacity bound, fresh results large enough, and
the exact write set on the reuse path -/
@[reducible] def XQ (R : RtInv) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 1).toNat < 2 ^ 40 ∧
    (((s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∨ xl.toNat + 1 ≤ (s'.regs 1).toNat) ∧
    (xl.toNat + 1 ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat ∧
      (natVal s'.mem zp.toNat (xl.toNat + 1) = natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat ∨
        (y.toNat = 0 ∧ r.toNat = 0 ∧ natVal s'.mem zp.toNat (xl.toNat + 1) = natVal s.mem zp.toNat (xl.toNat + 1))) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * (xl.toNat + 1))]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * (xl.toNat + 1))])

/-- the writes after `Mid` that keep `XM`: stack ranges or `p[0:m+1]` -/
def WsX (s : State) (p xl : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ (((s.regs 4).toNat - 4208 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 24) ∨
    ((s.regs 4).toNat - 16 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 8) ∨ (p ≤ r.1 ∧ r.2 ≤ p + 8 * (xl + 1)))

theorem WsX.ok {s : State} {p c xl : Nat} {ws : List (Nat × Nat)} (h : WsX s p xl ws) (hc : xl + 1 ≤ c) :
    WsOK s p c ws := by
  intro r hr
  obtain ⟨h1, h2⟩ := h r hr
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | h2 | h2
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨h2.1, by omega⟩)

/-- **A write to the stack or to `p[0:m+1]` keeps `XM`** -/
theorem XM.frame0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx : XM R L zp zc xl s p c M) {M2 : Janus.Arm64.Memory}
    {ws : List (Nat × Nat)} (hws : WsX s p xl.toNat ws) (hf : MemFrame M M2 ws) : XM R L zp zc xl s p c M2 := by
  refine ⟨hx.c40, fun hz => ?_⟩
  obtain ⟨hp, hc, hmf, hlf⟩ := hx.ex hz
  subst hp
  refine ⟨rfl, hc, ?_, ?_⟩
  · refine hmf.trans (hf.widen R.rt) fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz'⟩ := ho
    refine ⟨hrt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · have hsp0 := h.sp0
    refine ⟨fun a n hin hz' => ?_⟩
    rw [hf.readLE a n (outside_of_forall fun r hr => ?_)]
    · exact hlf.readLE a n hin hz'
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have hsep := h.lsep q hq
      simp only [win, outside_cons, outside_nil, and_true] at hsep hz'
      rcases (hws r hr).2 with h' | h' | h' <;> omega

/-- the facts after `mulAddVWW.abi0` returns (as `vww_after`, with `XM`) -/
theorem vww_afterX {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M1 w : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx : XM R L zp zc xl s p c M)
    (hf1 : MemFrame M M1 [((s.regs 4).toNat - 112, (s.regs 4).toNat - 40),
      ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)])
    (hfr : MemFrame M1 w [(p, p + 8 * xl.toNat), ((s.regs 4).toNat - 112 + 72, (s.regs 4).toNat - 112 + 80)]) :
    XM R L zp zc xl s p c w := by
  have hsp0 := h.sp0
  have hws1 : WsX s p xl.toNat [((s.regs 4).toNat - 112, (s.regs 4).toNat - 40),
      ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hws2 : WsX s p xl.toNat [(p, p + 8 * xl.toNat),
      ((s.regs 4).toNat - 112 + 72, (s.regs 4).toNat - 112 + 80)] := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  exact (hx.frame0 h hws1 hf1).frame0 (h.frame0 (hws1.ok h.cap) hf1) hws2 hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tailX (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zc xp xl y r : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx : XM R L zp zc xl s p c M) (hx0 : xl.toNat ≠ 0)
    (hy0 : y.toNat ≠ 0)
    (hps : M.readLE ((s.regs 4).toNat - 16) 8 = p) (hcs : M.readLE ((s.regs 4).toNat - 32) 8 = c)
    (hv : natVal M p xl.toNat + 2 ^ (64 * xl.toNat) * M.readLE ((s.regs 4).toNat - 40) 8 =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hAfter)
    (hsp : S.regs 4 = s.regs 4 - 104#64) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hpw := h.pw
  unfold Apart at hpw
  have r1 := h.sm; have r2 := h.sm1; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  have hp8 := h.p8; have htls := h.tls; have htacc := h.tacc
  have htb := h.tlsg.base
  have hcw := Janus.Spec.MemHash.readLE_lt64 M ((s.regs 4).toNat - 40) 8 (by decide)
  obtain ⟨cw, hcwv⟩ : ∃ cw, M.readLE ((s.regs 4).toNat - 40) 8 = cw := ⟨_, rfl⟩
  rw [hcwv] at hv hcw
  have hpw8 : M.accessible p (8 * (xl.toNat + 1)) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
  janus64_run [hm, r1, r2, hps, hcwv, htls, hfs, BitVec.msb_eq_decide,
    (show (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 by omega)] until [hNorm]
  have hst := h.frame0 (ws := [(p + 8 * xl.toNat, p + 8 * xl.toNat + 8)])
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; simp only; omega)
    (M2 := M.writeLE (p + 8 * xl.toNat) 8 cw) (by janus_frame)
  have hstX := hx.frame0 h (ws := [(p + 8 * xl.toNat, p + 8 * xl.toNat + 8)])
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; simp only; omega)
    (M2 := M.writeLE (p + 8 * xl.toNat) 8 cw) (by janus_frame)
  have hval : natVal (M.writeLE (p + 8 * xl.toNat) 8 cw) p (xl.toNat + 1) =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat := by
    rw [natVal_succ, Janus.Arm64.Memory.readLE_writeLE_self, ← hv, Nat.mod_eq_of_lt (by simpa using hcw)]
    congr 1
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine norm impl s _ p c (xl.toNat + 1) _ _ (fun s' n' hm' h0' h1' h2' hfs' hn' hv' hnm' =>
      ⟨hst.post hx0 hy0 s' n' hm' h0' h1' h2' hfs' hn' hv' hnm', ?xq⟩) hcap (by omega) (by omega)
    (by simpa only [Janus.Arm64.Memory.accessible_writeLE] using hpw8)
    hst.lr hst.fp (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hcs)
    hal hsp0 hsp1 hst.sacc h.ra47 (xl.toNat + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by show M.writeLE _ 8 cw = _; rw [Nat.mul_comm xl.toNat 8]) hval
  case xq =>
    show XQ R L zp zc xp xl y r s s'; unfold XQ; rw [h0', h2']
    refine ⟨hstX.c40, Or.inr hcap, fun hz => ?_⟩
    obtain ⟨hp, hc, hmf, hlf⟩ := hstX.ex hz
    refine ⟨hp, hc, Or.inl ?_, by rw [hm']; exact hmf, by rw [hm']; exact hlf⟩
    rw [hm', ← hp]; exact hval
  all_goals try janus64_simp
  all_goals first | exact hfs | exact h.x15.symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem vwwX (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc y r : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx : XM R L zp zc xl s p c M) (hx0 : xl.toNat ≠ 0)
    (hy0 : y.toNat ≠ 0)
    (hvx : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hMid) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h3 : S.regs 3 = BitVec.ofNat 64 (xl.toNat + 1))
    (h1 : S.regs 1 = BitVec.ofNat 64 c) (h7 : S.regs 7 = xp) (h6 : S.regs 6 = xl) (h8 : S.regs 8 = xc)
    (h9 : S.regs 9 = y) (h10 : S.regs 10 = r)
    (hsp : S.regs 4 = s.regs 4 - 104#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' ∧ XQ R L zp zc xp xl y r s s' := by
  have hV := vww_live impl hap R b' L'
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40
  have hsacc := h.sacc; have hal := h.al; have hinv := h.inv; have hp8 := h.p8; have hx48 := h.x48
  have hwrt := h.wrt; have hgrt := h.grt
  have hpw := h.pw; have hpg := h.pg; have hgw := h.gw
  unfold Apart at hpw hpg hgw
  have hza : M.accessible p (8 * xl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hzh : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hxa := h.xacc
  have hzx : p = xp.toNat ∨ Apart p (8 * xl.toNat) xp.toNat (8 * xl.toNat) := by
    rcases h.px with e | e
    · exact Or.inl e
    · right; unfold Apart at e ⊢; omega
  have hra := h.ra47
  have hpf := h.pf; have htw := h.tw
  unfold Apart at hpf htw
  janus64_run [hm, hfs, mod64_of_lt (a := c) (by omega), mod64_of_lt (a := p) (by omega), BitVec.msb_eq_decide]
    until [hAfter] calls [hV]
  rename_i _ _ _ _ _ w _ _ hv hc hfr hinvw hg _
  obtain ⟨hm2, hps, hcs⟩ := vww_after h (M1 := _) (by janus_frame) hfr (by janus64_simp) (by janus64_simp)
  have hx2 := vww_afterX h hx (M1 := _) (by janus_frame) hfr
  have hlo : natVal w p xl.toNat + 2 ^ (64 * xl.toNat) * w.readLE ((s.regs 4).toNat - 40) 8 =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat := by
    have hxw := h.xw; unfold Apart at hxw
    rw [show (s.regs 4).toNat - 40 = (s.regs 4).toNat - 112 + 72 by omega, hc, hv, Nat.mod_add_div, ← hvx]
    congr 2
    exact natVal_frame (rs := [((s.regs 4).toNat - 112, (s.regs 4).toNat - 40),
      ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)]) (by janus_frame)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine tailX impl R b L zp zc xp xl y r s p c L' b' w hm2 hx2 hx0 hy0 hps hcs hlo _ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals janus64_simp

end FvModexp.Amd64.MulAddWW
