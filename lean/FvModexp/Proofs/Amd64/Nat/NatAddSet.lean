import FvModexp.Proofs.Amd64.Nat.NatAddMid
import FvModexp.Proofs.Common.AsmVW
import FvModexp.Proofs.Common.DivmcBits

/-!
# `nat.add` (amd64): `case n == 0: return z.set(x)` from `+0x252` (after `z.make(m)`)

At `+0x252`: `AX = p`, `CX = c`, `DX = m`, `SI = m` (`len z`), `DI = xp`. `CMPQ DX, SI; MOVQ SI, BX; CMOVL DX, SI`;
`CMPQ DI, AX; JE ret`; spills to `0x60/0x70/0x80(RSP')`; `memmove(p, xp, 8 m)`; `return z[:m]`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatAdd

abbrev hSet : Nat := segAddr Extracted.program fn + 0x252

structure SetMid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory) : Prop where
  gok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4288 < (s.regs 4).toNat
  tlsg : TlsG s
  trt : Outside (s.fsBase.toNat - 8) 8 R.rt
  tw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 4288) (4288 + 80)
  x15 : s.xmm 15 = 0#128
  df0 : s.df = false
  g48 : (s.regs 14).toNat + 24 ≤ 2 ^ 48
  al : (s.regs 4).toNat % 8 = 0
  sp0 : 4288 ≤ (s.regs 4).toNat
  sp1 : (s.regs 4).toNat + 80 ≤ 2 ^ 48
  wrt : Outside ((s.regs 4).toNat - 4288) (4288 + 80) R.rt
  gw : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4288) (4288 + 80)
  grt : Outside ((s.regs 14).toNat + 16) 8 R.rt
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  xl40 : xl.toNat < 2 ^ 40
  x0 : 0 < xl.toNat
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sacc : M.accessible ((s.regs 4).toNat - 4288) (4288 + 80) true = true
  gacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8
  tacc : M.accessible (s.fsBase.toNat - 8) 8 false = true
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  cap : xl.toNat ≤ c
  c41 : c < 2 ^ 41
  c40 : xl.toNat < 2 ^ 39 → c < 2 ^ 40
  ru : xl.toNat ≤ zc.toNat → p = zp.toNat ∧ c = zc.toNat
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) ((s.regs 4).toNat - 4288) (4288 + 80)
  pg : Apart p (8 * c) ((s.regs 14).toNat + 16) 8
  pf : Apart p (8 * c) (s.fsBase.toNat - 8) 8
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  xw : Apart xp.toNat (8 * xl.toNat) ((s.regs 4).toNat - 4288) (4288 + 80)
  xv : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat
  xn : M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0
  ext : LiveExt R L L'
  bud : b - makeCost xl.toNat ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4288 80)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s 4288 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)]
  mv : ∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k]

theorem SetMid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Janus.Arm64.Memory}
    (h : SetMid R b L zp zc xp xl s p c L' b' M) (hy0 : yl.toNat = 0)
    (hF : MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 4288, (s.regs 4).toNat - 8), (p, p + 8 * xl.toNat)]))
    (hLF : LiveFrame M M' L' [(p, p + 8 * xl.toNat)])
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M'))
    (hcp : M'.readLE p (8 * xl.toNat) = M.readLE xp.toNat (8 * xl.toNat))
    (hnz : M'.readLE (p + 8 * (xl.toNat - 1)) 8 = M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8)
    (s' : State) (hm : s'.mem = M') (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 3).toNat = xl.toNat)
    (h2 : (s'.regs 1).toNat = c) (hfs : s'.fsBase = s.fsBase) (hdf' : s'.df = false) :
    PostR 4288 R b L zp zc xp xl yp yl s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  have hneed : need xl yl = xl.toNat := by unfold need mx; rw [if_pos (by omega)]; omega
  refine ⟨?_, fun hle => ⟨h0.trans (h.ru (by omega)).1, h2.trans (h.ru (by omega)).2⟩, fun hx => by rw [h2]; exact h.c40 (by unfold mx at hx; omega)⟩
  refine ⟨hfs, p, xl.toNat, c, h0, h1, h2, ?_, Or.inr ?_, hcap, by unfold mx; omega, L', b', h.ext,
    by rw [hneed]; exact h.bud, hinv, fun _ => ⟨h.p8, h.pheld, by rw [hF.accessible]; exact h.pacc, h.p48⟩, h.ror, ?_, ?_⟩
  · show s'.mem.readLE p (8 * xl.toNat) = _ + natVal s.mem yp.toNat yl.toNat
    rw [hcp, hy0, natVal_zero, Nat.add_zero]; exact h.xv
  · rw [hnz]; exact h.xn
  · refine h.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz⟩ := ho
    refine ⟨hrt, by omega, ?_⟩
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · omega
    · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n (h.ext.inRanges_old hin) ?_]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      simp only [outside_cons, outside_nil, and_true] at hz ⊢
      rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
      · omega
      · have := hap q hq; unfold Apart at this; omega

theorem setmid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M : Janus.Arm64.Memory} (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false) (hz : xl.toNat ≤ zc.toNat)
    (hF : MemFrame s.mem M (win s 4288 80))
    (r1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (r2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) :
    SetMid R b L zp zc xp xl s zp.toNat zc.toNat L b M := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, _, hxw, hyacc, hy48, hyh, hyw, hinv, _, hmv⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzf, hzx, hzy⟩ := hzw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw hyw
  have htw' := htw
  unfold Apart at hga htw'
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    ra47 := hra, xl40 := hx40, x0 := hx0, lr := r1, fp := r2,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hF.accessible]; exact htg.readable,
    tls := by rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hz, c41 := by omega, c40 := fun _ => hz40, ru := fun _ => ⟨rfl, rfl⟩, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pf := hzf, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := natVal_frame hF (hFo _ _ (by omega)),
    xn := by
      rw [hF.readLE _ _ (hFo _ _ (by omega))]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_win hF hout hb' hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := win s 4288 80) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega),
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

theorem setmid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} {M0 m : Janus.Arm64.Memory} {ptr round c : Nat} {cs : List (Nat × Nat)}
    (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hzlt : zc.toNat < xl.toNat)
    (hF : MemFrame s.mem M0 (win s 4288 80))
    (r1 : M0.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (r2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 4288 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    SetMid R b L zp zc xp xl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, _, hxw, hyacc, hy48, hyh, hyw, hinv0, _, hmv⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have htw' := htw
  unfold Apart at hga htw'
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgo := outside_of_inRanges hgr hIn
  have hto := outside_of_inRanges htr hIn
  have hcw : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat - 40 ≤ a) → Outside a n R.rt → Outside a n (R.rt ++ cs) := by
    intro a n h hr
    rw [outside_append]
    refine ⟨hr, outside_of_forall fun r hr' => ?_⟩
    have := hcs r hr'; omega
  have rd : ∀ a, (s.regs 4).toNat - 40 ≤ a → a + 8 ≤ (s.regs 4).toNat + 80 → m.readLE a 8 = M0.readLE a 8 :=
    fun a h1 h2 => hMF.readLE a 8 (hcw a 8 (by omega) (hout.of_sub (by omega) (by omega)))
  have hFo : ∀ a n, (a + n ≤ (s.regs 4).toNat - 4288 ∨ (s.regs 4).toNat + 80 ≤ a) → Outside a n (win s 4288 80) := by
    intro a n h; simp only [win, outside_cons, outside_nil, and_true]; omega
  have hxk : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → m.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [held_keep (hxh.sub h1 h2) hLF hMF (outside_of_forall fun r hr => by have := hcs r hr; omega),
      hF.readLE _ _ (hFo _ _ (by omega))]
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra, xl40 := hx40, x0 := hx0,
    lr := by rw [rd _ (by omega) (by omega)]; exact r1, fp := by rw [rd _ (by omega) (by omega)]; exact r2,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ (hcw _ _ (by omega) hgr)]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hMF.accessible, hF.accessible]; exact htg.readable,
    tls := by rw [hMF.readLE _ _ (hcw _ _ (by omega) htr), hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hc1, c41 := by omega, c40 := fun _ => by omega, ru := fun h => absurd h (by omega), p8 := h8, p48 := by omega,
    pacc := Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pf := by unfold Apart; omega,
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := hxk _ _ (Nat.le_refl _) (Nat.le_refl _),
    xn := by
      rw [hxk _ _ (by omega) (by omega)]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := hext, bud := by omega, inv := hinv,
    lsep := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp only [win, outside_cons, outside_nil, and_true]; omega,
    ror := Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, by
      simp only [outside_append, win, outside_cons, outside_nil, and_true] at h
      exact hcw a n (by omega) h.1.1⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [win, outside_cons, outside_nil, and_true]; omega,
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

end FvModexp.Amd64.NatAdd

namespace FvModexp.Amd64.NatAdd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setTail (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibNatAdd.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : SetMid R b L zp zc xp xl s p c L' b' M) (hy0 : yl.toNat = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h2 : S.regs 2 = xl) (h1 : S.regs 1 = BitVec.ofNat 64 c) (h7 : S.regs 7 = xp) (h6 : S.regs 6 = xl)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibNatAdd.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hx0 := h.x0; have hx48 := h.x48
  have r1 := h.lr; have r2 := h.fp; have hsacc := h.sacc; have hal := h.al; have hinv := h.inv
  have hpacc : M.accessible p (8 * xl.toNat) true = true :=
    Janus.Arm64.Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc := h.xacc; have hra := h.ra47; have hwrt := h.wrt
  have hpw := h.pw; have hxw := h.xw; have hgw := h.gw; have hpf := h.pf; have hpg := h.pg; have htw := h.tw
  unfold Apart at hpw hxw hgw hpf hpg htw
  have hph : InRanges p (xl.toNat * 8) L' ∨ Outside p (xl.toNat * 8) R.rt := h.pheld.sub (Nat.le_refl _) (by omega)
  have hx15' := h.x15
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, xl.toNat * 8] := fun d src => h.mv d src _ (by omega)
  have hg48 : (s.regs 14).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc; have htacc := h.tacc; have htls := h.tls; have htb := h.tlsg.base; have htrt := h.trt
  have hgok : M.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 152 := by rw [h.grd]; have := h.gok; omega
  janus64_run [hm, r1, r2, hfs, BitVec.msb_eq_decide, FvModexp.mod64_of_lt c (by omega), FvModexp.mod64_of_lt p (by omega)] calls [hmv]
  · -- `p = xp`: no copy
    rename_i hpx
    have hpx' : xp.toNat = p := by omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, h.post hy0 (MemFrame.refl _ _) ⟨fun _ _ _ _ => rfl⟩ h.inv (by rw [hpx']) (by rw [hpx'])
      _ rfl ?_ ?_ ?_ ?_ ?_⟩
    all_goals try janus64_simp
    all_goals first | exact hx15'.symm | exact hdf | omega
  · rename_i _ _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp
    have hcp' := Asm.readLE_of_copied hcp
    have hsub : Mem.Copied _ m (p + 8 * (xl.toNat - 1)) (xp.toNat + 8 * (xl.toNat - 1)) 8 := fun i hi => by
      have := hcp (8 * (xl.toNat - 1) + i) (by omega)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at this; exact this
    have hnz' := Asm.readLE_of_copied hsub
    have hW : MemFrame M ((((M.writeLE ((s.regs 4).toNat - 48) 8 c).writeLE ((s.regs 4).toNat - 32) 8 xl.toNat).writeLE
        ((s.regs 4).toNat - 16) 8 p).writeLE ((s.regs 4).toNat - 152) 8 6182886) [((s.regs 4).toNat - 152, (s.regs 4).toNat - 144), ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40),
          ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8)] := by janus_frame
    have rdW : ∀ a n, (a + n ≤ (s.regs 4).toNat - 152 ∨ (s.regs 4).toNat - 8 ≤ a) →
        ((((M.writeLE ((s.regs 4).toNat - 48) 8 c).writeLE ((s.regs 4).toNat - 32) 8 xl.toNat).writeLE
          ((s.regs 4).toNat - 16) 8 p).writeLE ((s.regs 4).toNat - 152) 8 6182886).readLE a n = M.readLE a n := fun a n h' =>
      hW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [show xl.toNat * 8 = 8 * xl.toNat by omega] at hF2 hLF2 hcp'
    refine ⟨⟨?_, ?_, ?_, ?_⟩, h.post hy0 (hW.trans hF2 fun a n ho => ?fr) ⟨fun a n hin ho => ?lf⟩ hinv2 ?cp ?nz _ rfl
      ?_ ?_ ?_ ?_ ?_⟩
    case fr =>
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2'⟩ := ho
      and_intros <;> first | exact hr | omega
    case lf =>
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this
      rw [hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ ho, rdW a n (by omega)]
    case cp => rw [hcp', rdW _ _ (by omega)]
    case nz => rw [hnz', rdW _ _ (by omega)]
    all_goals try janus64_simp
    all_goals first | exact hx15'.symm | omega

end FvModexp.Amd64.NatAdd
