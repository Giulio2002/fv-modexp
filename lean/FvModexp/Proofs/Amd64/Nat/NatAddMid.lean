import FvModexp.Proofs.Amd64.Nat.NatAddNorm
import FvModexp.Proofs.Common.DivmcMem

/-!
# `nat.add` (arm64): the facts at the segment boundaries after `z.make(m + 1)` (`+0x94` … return)

`Mid … p c L' b' M`: the result array `(p, c)` has been chosen (`z`'s own array when `zc ≥ m + 1`, else a fresh
`makeslice` block), the entry's frame words and spills are in place, and the runtime facts of the entry state carry
over to `M` with the live set `L'` and budget `b'`. It is kept by the two internal calls (`Mid.frame`: `addVV.abi0`
writes `z[:n]` and its result slot, `addVW` writes `z[n:m]` and its own stack) and by the store `z[m] = c`
(`Mid.store`), and gives `nat.add`'s postcondition (`Mid.post`).

Stack (entry `RSP`, return address at `RSP`): saved `RBP` at `RSP - 8`, `RSP' = RSP - 144`; locals `0x50(RSP') = RSP - 64`
(cap), `0x68(RSP') = RSP - 40` (`m + 1`), `0x78(RSP') = RSP - 24` (`p`); spills `xp, xl, xc, yp, yl` at `RSP + 32 … 64`.
Callee windows: `addVV.abi0` frame `[RSP - 152, RSP - 64)` (result word `RSP - 72`); `addVW` (`stk 4136`, `above 40`,
callee `RSP = RSP - 152`) `[RSP - 4288, RSP - 112)`; runtime calls `[RSP - 4248, RSP - 152) ∪ [RSP - 144, RSP - 120)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatAdd

/-- The join of the reuse and allocation paths of `z.make(m + 1)`. -/
abbrev hMid : Nat := segAddr Extracted.program fn + 0xe6

/-- The segment-boundary facts after the result array `(p, c)` is chosen (see the module doc). -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  -- entry facts (about `s` only)
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
  yl40 : yl.toNat < 2 ^ 40
  -- frame words and spills
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  sxp : M.readLE ((s.regs 4).toNat + 32) 8 = xp.toNat
  sxl : M.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat
  sxc : M.readLE ((s.regs 4).toNat + 48) 8 = xc.toNat
  syl : M.readLE ((s.regs 4).toNat + 64) 8 = yl.toNat
  sm1 : M.readLE ((s.regs 4).toNat - 40) 8 = xl.toNat + 1
  sacc : M.accessible ((s.regs 4).toNat - 4288) (4288 + 80) true = true
  gacc : M.accessible ((s.regs 14).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8
  tacc : M.accessible (s.fsBase.toNat - 8) 8 false = true
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  -- the result array
  cap : xl.toNat + 1 ≤ c
  c41 : c < 2 ^ 41
  c40 : xl.toNat < 2 ^ 39 → c < 2 ^ 40
  ru : xl.toNat + 1 ≤ zc.toNat → p = zp.toNat ∧ c = zc.toNat
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) ((s.regs 4).toNat - 4288) (4288 + 80)
  pg : Apart p (8 * c) ((s.regs 14).toNat + 16) 8
  pf : Apart p (8 * c) (s.fsBase.toNat - 8) 8
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  py : p = yp.toNat ∨ Apart p (8 * c) yp.toNat (8 * yl.toNat)
  -- the operands
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  xheld : Held R L' xp.toNat (8 * xl.toNat)
  xw : Apart xp.toNat (8 * xl.toNat) ((s.regs 4).toNat - 4288) (4288 + 80)
  yacc : M.accessible yp.toNat (8 * yl.toNat) false = true
  y48 : yp.toNat + 8 * yl.toNat ≤ 2 ^ 48
  yheld : Held R L' yp.toNat (8 * yl.toNat)
  yw : Apart yp.toNat (8 * yl.toNat) ((s.regs 4).toNat - 4288) (4288 + 80)
  -- runtime
  ext : LiveExt R L L'
  bud : b - makeCost (xl.toNat + 1) ≤ b'
  inv : R.inv b' L' (s.regs 14).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4288 80)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ win s 4288 80 ++ [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)]
  mv : ∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k]

theorem outside_of_inRanges {a n p k : Nat} {rs : List (Nat × Nat)} (h : Outside a n rs) (hin : InRanges p k rs) :
    a + n ≤ p ∨ p + k ≤ a := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem h hr
  omega

theorem liveFrame_of_memFrame {m m' : Janus.Arm64.Memory} {L ws : List (Nat × Nat)} (h : MemFrame m m' ws) :
    LiveFrame m m' L ws :=
  ⟨fun a n _ ho => h.readLE a n ho⟩

/-- A held range outside a runtime call's stack window keeps its bytes. -/
theorem held_keep {R : RtInv} {L cs : List (Nat × Nat)} {M0 m : Janus.Arm64.Memory} {a n : Nat} (hh : Held R L a n)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs)) (ho : Outside a n cs) :
    m.readLE a n = M0.readLE a n := by
  rcases hh with hin | hout
  · exact hLF.readLE a n hin trivial
  · exact hMF.readLE a n (by rw [outside_append]; exact ⟨hout, ho⟩)

/-- The stack ranges and array parts a callee may write. -/
def WsOK (s : State) (p c : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ (((s.regs 4).toNat - 4288 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40) ∨
    ((s.regs 4).toNat - 32 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 8) ∨ (p ≤ r.1 ∧ r.2 ≤ p + 8 * c))

/-- **A call keeps `Mid`**: the callee wrote only inside `R.rt`, its stack window parts below the spills, and the
result array (`WsOK`), extending the live set. -/
theorem Mid.frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) {M2 : Janus.Arm64.Memory} {ws : List (Nat × Nat)} {L'' : List (Nat × Nat)}
    {b'' : Nat} (hws : WsOK s p (xl.toNat + 1) ws) (hf : MemFrame M M2 (R.rt ++ ws)) (hl : LiveFrame M M2 L' ws)
    (hext : LiveExt R L' L'') (hb : b' ≤ b'') (hinv : R.inv b'' L'' (s.regs 14).toNat (view R.rt L'' M2)) :
    Mid R b L zp zc xp xl xc yp yl s p c L'' b'' M2 := by
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw hgw hpg
  -- a range in the window below / between the spills, or apart from the array, is outside `R.rt ++ ws`
  have key : ∀ a n, (s.regs 4).toNat - 4288 ≤ a → a + n ≤ (s.regs 4).toNat + 80 →
      (∀ r ∈ ws, a + n ≤ r.1 ∨ r.2 ≤ a) → Outside a n (R.rt ++ ws) := by
    intro a n h1 h2 h3
    simp only [outside_append]
    exact ⟨h.wrt.of_sub h1 (by omega), outside_of_forall h3⟩
  have rd : ∀ a, ((s.regs 4).toNat - 40 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat - 32 ∨ (s.regs 4).toNat - 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 80) →
      M2.readLE a 8 = M.readLE a 8 := by
    intro a ha
    refine hf.readLE a 8 (key a 8 (by omega) (by omega) fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  refine { h with
      lr := ?_
      fp := ?_
      sxp := ?_
      sxl := ?_
      sxc := ?_
      syl := ?_
      sm1 := ?_
      sacc := ?_
      gacc := ?_
      grd := ?_
      tacc := ?_
      tls := ?_
      pacc := ?_
      pheld := hext.held h.pheld
      xacc := ?_
      xheld := hext.held h.xheld
      yacc := ?_
      yheld := hext.held h.yheld
      ext := h.ext.trans hext
      bud := Nat.le_trans h.bud hb
      inv := hinv
      lsep := ?_
      mf := ?_
      lf := ?_ }
  · rw [rd _ (by omega)]; exact h.lr
  · rw [rd _ (by omega)]; exact h.fp
  · rw [rd _ (by omega)]; exact h.sxp
  · rw [rd _ (by omega)]; exact h.sxl
  · rw [rd _ (by omega)]; exact h.sxc
  · rw [rd _ (by omega)]; exact h.syl
  · rw [rd _ (by omega)]; exact h.sm1
  · rw [hf.accessible]; exact h.sacc
  · rw [hf.accessible]; exact h.gacc
  · rw [← h.grd]
    refine hf.readLE _ _ ?_
    simp only [outside_append]
    refine ⟨h.grt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · rw [hf.accessible]; exact h.tacc
  · rw [← h.tls]
    have htw := h.tw; have hpf := h.pf
    unfold Apart at htw hpf
    refine hf.readLE _ _ ?_
    simp only [outside_append]
    refine ⟨h.trt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · rw [hf.accessible]; exact h.pacc
  · rw [hf.accessible]; exact h.xacc
  · rw [hf.accessible]; exact h.yacc
  · intro r hr
    obtain ⟨ns, rfl, hn, -⟩ := hext
    rcases List.mem_append.1 hr with hr | hr
    · exact h.lsep r hr
    · have hin := (hn r hr).1
      have hw := h.wrt
      simp only [win, outside_cons, outside_nil, and_true]
      have := outside_of_inRanges hw hin
      omega
  · refine h.mf.trans hf fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1⟩, hz⟩ := ho
    refine ⟨hrt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h'
    · omega
    · omega
    · rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
      · omega
      · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hl.readLE a n (h.ext.inRanges_old hin) (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have hsep := h.lsep q (h.ext.mem_old hq)
      simp only [win, outside_cons, outside_nil, and_true] at hsep hz
      rcases (hws r hr).2 with h' | h' | h'
      · omega
      · omega
      · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
        · omega
        · have := hap q hq; unfold Apart at this; omega

/-- **A frame without allocation keeps `Mid`** (stack stores, `addVV.abi0`): the writes `ws` are in the window (outside
`R.rt`) or in the result array (held), so the invariant and the live objects carry over. -/
theorem Mid.frame0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) {M2 : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (hws : WsOK s p (xl.toNat + 1) ws) (hf : MemFrame M M2 ws) : Mid R b L zp zc xp xl xc yp yl s p c L' b' M2 := by
  have hsp0 := h.sp0; have hcap := h.cap
  refine h.frame hws (hf.widen R.rt) (liveFrame_of_memFrame hf) (LiveExt.refl R L') (Nat.le_refl _) ?_
  refine RtInv.inv_frame' hf (fun r hr => ?_) h.inv
  have h0 := (hws r hr).1
  rcases (hws r hr).2 with h' | h' | h'
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact (h.pheld.sub h'.1 (by omega)).symm

/-- A read in the window that the callee's writes avoid is unchanged by the call. -/
theorem Mid.read {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) {M2 : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (hf : MemFrame M M2 (R.rt ++ ws)) {a : Nat} (h1 : (s.regs 4).toNat - 4288 ≤ a) (h2 : a + 8 ≤ (s.regs 4).toNat + 80)
    (hws : ∀ r ∈ ws, a + 8 ≤ r.1 ∨ r.2 ≤ a) : M2.readLE a 8 = M.readLE a 8 :=
  hf.readLE a 8 (by simp only [outside_append]; exact ⟨h.wrt.of_sub h1 (by omega), outside_of_forall hws⟩)

/-- **The store `z[i] = v`** (inside the result array) keeps `Mid`. -/
theorem Mid.store {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) {a : Nat} (v : Nat) (h1 : p ≤ a) (h2 : a + 8 ≤ p + 8 * (xl.toNat + 1)) :
    Mid R b L zp zc xp xl xc yp yl s p c L' b' (M.writeLE a 8 v) := by
  have hpw := h.pw; have hpg := h.pg; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw hpg
  have rd : ∀ x, (s.regs 4).toNat - 4288 ≤ x → x + 8 ≤ (s.regs 4).toNat + 80 → (M.writeLE a 8 v).readLE x 8 = M.readLE x 8 :=
    fun x hx1 hx2 => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine { h with
      lr := ?_
      fp := ?_
      sxp := ?_
      sxl := ?_
      sxc := ?_
      syl := ?_
      sm1 := ?_
      sacc := ?_
      gacc := ?_
      grd := ?_
      tacc := ?_
      tls := ?_
      pacc := ?_
      xacc := ?_
      yacc := ?_
      inv := inv_store_held h.inv (h.pheld.sub h1 (by omega))
      mf := ?_
      lf := ?_ }
  · rw [rd _ (by omega) (by omega)]; exact h.lr
  · rw [rd _ (by omega) (by omega)]; exact h.fp
  · rw [rd _ (by omega) (by omega)]; exact h.sxp
  · rw [rd _ (by omega) (by omega)]; exact h.sxl
  · rw [rd _ (by omega) (by omega)]; exact h.sxc
  · rw [rd _ (by omega) (by omega)]; exact h.syl
  · rw [rd _ (by omega) (by omega)]; exact h.sm1
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using h.sacc
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using h.gacc
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h.grd
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using h.tacc
  · have hpf := h.pf; unfold Apart at hpf
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h.tls
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using h.pacc
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using h.xacc
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using h.yacc
  · rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · exact MemFrame.writeLE_inRanges h.mf v ⟨(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat), by simp, h1, by simp only; omega⟩
    · obtain ⟨r, hr, hr1, hr2⟩ := hin
      exact MemFrame.writeLE_inRanges h.mf v ⟨r, by simp [hr], by omega, by omega⟩
  · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
    · exact LiveFrame.writeLE_ws h.lf v ⟨(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat), by simp, h1, by simp only; omega⟩
    · exact LiveFrame.writeLE h.lf v (ApartAll.outside (fun r hr => by
        have := hap r hr; unfold Apart at this ⊢; omega))

/-- **The postcondition** from `Mid` at the return (`s'.mem = M`, result `(p, n', c)`). -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Janus.Arm64.Memory}
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat) (s' : State) (n' : Nat)
    (hm : s'.mem = M) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 3).toNat = n') (h2 : (s'.regs 1).toNat = c)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = false) (hn : n' ≤ xl.toNat + 1)
    (hv : natVal M p n' = natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat) (hnorm : NatNorm M p n') :
    PostX 4288 R b L zp zc xp xl yp yl s s' := by
  subst hm
  have hneed : need xl yl = xl.toNat + 1 := by
    unfold need mx; rw [if_neg (by omega)]; omega
  refine ⟨⟨?_, fun hle => ⟨h0.trans (h.ru (by omega)).1, h2.trans (h.ru (by omega)).2⟩,
    fun hx => by rw [h2]; exact h.c40 (by unfold mx at hx; omega)⟩, h.mf, h.lf⟩
  have hfr := frames_of_x (zp := zp) (zc := zc) h.mf h.lf
  refine ⟨hfs, hdf.trans h.df0.symm, p, n', c, h0, h1, h2, hv, hnorm, by have := h.cap; omega, by unfold mx; omega, L', b', h.ext, ?_, h.inv,
    fun _ => ⟨h.p8, h.pheld, h.pacc, h.p48⟩, h.ror, hfr.1, hfr.2⟩
  rw [hneed]; exact h.bud


theorem inv_win {R : RtInv} {b g : Nat} {L : List (Nat × Nat)} {s : State} {m m' : Janus.Arm64.Memory}
    {stk above : Nat} (hF : MemFrame m m' (win s stk above)) (hout : Outside ((s.regs 4).toNat - stk) (stk + above) R.rt)
    (hsp : stk ≤ (s.regs 4).toNat) (hi : R.inv b L g (view R.rt L m)) : R.inv b L g (view R.rt L m') := by
  refine RtInv.inv_frame' hF (fun r hr => ?_) hi
  simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact Or.inl (hout.of_sub (Nat.le_refl _) (by simp; omega))

/-- The facts of the entry state every constructor needs (amd64 `CallEnv` destructured). -/
theorem preS_env {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4288 < (s.regs 4).toNat ∧ 4288 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 80 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4288) (4288 + 80) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

/-- **`Mid` on the reuse path** (`zc ≥ m + 1`, amd64). -/
theorem mid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M : Janus.Arm64.Memory} (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) (hyx : yl.toNat ≤ xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false) (hz : xl.toNat + 1 ≤ zc.toNat)
    (hF : MemFrame s.mem M (win s 4288 80))
    (r1 : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (r2 : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r3 : M.readLE ((s.regs 4).toNat + 32) 8 = xp.toNat) (r4 : M.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat)
    (r5 : M.readLE ((s.regs 4).toNat + 48) 8 = xc.toNat) (r6 : M.readLE ((s.regs 4).toNat + 64) 8 = yl.toNat)
    (r7 : M.readLE ((s.regs 4).toNat - 40) 8 = xl.toNat + 1) :
    Mid R b L zp zc xp xl xc yp yl s zp.toNat zc.toNat L b M := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, _, _, hxw, hyacc, hy48, hyh, hyw, hinv, _, hmv⟩ := hpre
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
    ra47 := hra, xl40 := hx40, yl40 := hy40, lr := r1, fp := r2, sxp := r3, sxl := r4, sxc := r5,
    syl := r6, sm1 := r7, sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hF.accessible]; exact htg.readable,
    tls := by rw [hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := hz, c41 := by omega, c40 := fun _ => hz40, ru := fun _ => ⟨rfl, rfl⟩, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pg := hzg, pf := hzf, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id, py := hzy.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xheld := hxh, xw := by unfold Apart; omega,
    yacc := by rw [hF.accessible]; exact hyacc, y48 := hy48, yheld := hyh, yw := by unfold Apart; omega,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_win hF hout hb' hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := win s 4288 80) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega),
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

theorem held_apart_fresh {R : RtInv} {L : List (Nat × Nat)} {a n ptr k : Nat} (h : Held R L a n)
    (hAp : ApartAll ptr k L) (hIn : InRanges ptr k R.rt) : Apart ptr k a n := by
  rcases h with ⟨q, hq, h1, h2⟩ | ho
  · have := hAp q hq; unfold Apart at this ⊢; omega
  · have := outside_of_inRanges ho hIn; unfold Apart; omega

/-- **`Mid` on the allocation path** (amd64): `makeslice(Word, m + 1, m + 5)` whose stack ranges `cs` lie in
`[RSP - 4288, RSP - 40)` returned `[ptr, ptr + round)`. -/
theorem mid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M0 m : Janus.Arm64.Memory} {ptr round : Nat} {cs : List (Nat × Nat)}
    (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) (hyx : yl.toNat ≤ xl.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hzlt : zc.toNat < xl.toNat + 1)
    (hF : MemFrame s.mem M0 (win s 4288 80))
    (r1 : M0.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8) (r2 : M0.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (r3 : M0.readLE ((s.regs 4).toNat + 32) 8 = xp.toNat) (r4 : M0.readLE ((s.regs 4).toNat + 40) 8 = xl.toNat)
    (r5 : M0.readLE ((s.regs 4).toNat + 48) 8 = xc.toNat) (r6 : M0.readLE ((s.regs 4).toNat + 64) 8 = yl.toNat)
    (r7 : M0.readLE ((s.regs 4).toNat - 40) 8 = xl.toNat + 1)
    (hcs : ∀ r ∈ cs, (s.regs 4).toNat - 4288 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 40)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * (xl.toNat + 5) ≤ round) (hcost : round ≤ makeCost (xl.toNat + 1)) :
    Mid R b L zp zc xp xl xc yp yl s ptr (xl.toNat + 5) (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, _, _, hxw, hyacc, hy48, hyh, hyw, hinv0, _, hmv⟩ := hpre
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
  have hpa : InRanges ptr (8 * (xl.toNat + 5)) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩
  exact {
    gok := hg3, tlsg := htg, trt := htr, tw := htw, x15 := hx15, df0 := hdf, g48 := hg1, al := hal, sp0 := hb',
    sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr, ra47 := hra, xl40 := hx40, yl40 := hy40,
    lr := by rw [rd _ (by omega) (by omega)]; exact r1, fp := by rw [rd _ (by omega) (by omega)]; exact r2,
    sxp := by rw [rd _ (by omega) (by omega)]; exact r3, sxl := by rw [rd _ (by omega) (by omega)]; exact r4,
    sxc := by rw [rd _ (by omega) (by omega)]; exact r5, syl := by rw [rd _ (by omega) (by omega)]; exact r6,
    sm1 := by rw [rd _ (by omega) (by omega)]; exact r7,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ (hcw _ _ (by omega) hgr)]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    tacc := by rw [hMF.accessible, hF.accessible]; exact htg.readable,
    tls := by rw [hMF.readLE _ _ (hcw _ _ (by omega) htr), hF.readLE _ _ (hFo _ _ (by omega))]; exact htg.g,
    cap := by omega, c41 := by omega, c40 := fun _ => by omega, ru := fun h => absurd h (by omega), p8 := h8, p48 := by omega,
    pacc := Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega, pg := by unfold Apart; omega, pf := by unfold Apart; omega, pheld := Or.inl hpa,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    py := Or.inr ((held_apart_fresh hyh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xheld := hext.held hxh,
    xw := by unfold Apart; omega,
    yacc := by rw [hMF.accessible, hF.accessible]; exact hyacc, y48 := hy48, yheld := hext.held hyh,
    yw := by unfold Apart; omega,
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
