import FvModexp.Proofs.Amd64.Top.RunC2RA
import FvModexp.Proofs.Amd64.Top.RunC2Lem
import FvModexp.Proofs.Amd64.Top.RunC2Lem3
import FvModexp.Proofs.Amd64.Top.RunC2V

/-! # `Run` (amd64): after `Mod` / `exp` returned — `Bytes(z)` and on to `V` (shared by both compute paths)

At the `Bytes` call site (`fn + 0xb94` after `Mod`, or `fn + 0xbbd` after `exp`), `z = base` (`e - 136`) holds the result
value `v` (the callee's `IntPost`). `CALL (*Int).Bytes` (return `fn + 0xb99`, then `JMP V`; or return `V = fn + 0xbc5`)
gives `v`'s minimal big-endian bytes: the state `RelV` at `V`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- `RSP - 608 + 472 = RSP - 136` (asm s83: a named closer; `omega` in `c2B`'s context took 60 s) -/
theorem c2B_sp136 (x : BitVec 64) (h : 608 ≤ x.toNat) : (x - 608#64 + 472#64).toNat = x.toNat - 136 := by
  rw [BitVec.toNat_add, BitVec.toNat_sub]; simp; omega

theorem c2B_le40 (e : Nat) : e - 136 + 32 ≤ e + 40 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem c2B (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (stkM aboveM : Nat)
    (hBy : RunIface.BytesSpec impl R stkM aboveM) (hsv : RunIface.Serves R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (Q : Janus.Amd64.Outcome → Prop)
    (W : Nat) (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144)
    (ha8 : 8 ≤ aboveM)
    (hglob : RunIface.Globals R s.mem (win s W 40))
    (L1 : List (Nat × Nat)) (b1 : Nat) (T : State) (hrel : RelD R b L c p len cp s ret 3 3 (cstD 3) L1 b1 T)
    (hk : ∀ V Lk bk, RelV R b L p len s ret W Lk bk V → V.rip = BitVec.ofNat 64 pcCV →
      Reaches ((LibRun.program.link impl).withExit ret) V Q)
    (B : Nat) (ys : List Nat) (v rs1 rs2 : Nat) (sc s' : State)
    (hIP : ∀ t : State, t.regs 4 = T.regs 4 - 8#64 → t.mem = sc.mem → t.regs 14 = s.regs 14 → t.fsBase = s.fsBase →
      RunIface.IntPre R b1 B L1 stkM aboveM (((s.regs 4).toNat - 136) :: ys) t)
    (hsc4 : sc.regs 4 = T.regs 4 - 8#64) (hscm : sc.mem = T.mem.writeLE ((s.regs 4).toNat - 616) 8 rs1)
    (hsc14 : sc.regs 14 = s.regs 14) (hscfs : sc.fsBase = s.fsBase)
    (hpost : RunIface.IntPost R b1 B L1 stkM aboveM ((s.regs 4).toNat - 136) v sc s')
    (hrg : s'.mem.regions = sc.mem.regions)
    (h4' : s'.regs 4 = T.regs 4) (h5' : s'.regs 5 = T.regs 5) (h14' : s'.regs 14 = s.regs 14)
    (hx' : s'.xmm 15 = 0) (hfs' : s'.fsBase = s.fsBase) (hdf' : s'.df = false)
    (hr0' : (s'.regs 0).toNat = (s.regs 4).toNat - 136)
    (hpc' : (s'.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0xb94) ∧ rs2 = 6639321) ∨
      (s'.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0xbbd) ∧ rs2 = 6639365))
    (hv : v = resV s p len) (hvlt : v < opV s p len 2)
    (hBB : B + RunIface.BytesBudget RunIface.maxW ≤ b1)
    (hbfin : ∀ b2 b3 lb, lb ≤ RunIface.maxW → b1 - B ≤ b2 → b2 - RunIface.BytesBudget lb ≤ b3 →
      b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ b3) :
    Reaches ((LibRun.program.link impl).withExit ret) s' Q := by
  have henvW0 := henvW
  have hrel0 := hrel
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henvW
  simp only [regSP, Janus.Amd64.GoABI.regG] at hb' ha hw hout hal hga hgr
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, -, -, -, -, -, -, hs3, -, -, -, -, -, hl2, -, -, -,
    hdS, -, -, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  simp only [stk] at hLsS hMF
  have hglob0 := hglob
  obtain ⟨-, -, -, -, -, -, -, -, hgrt, hgw, -⟩ := hglob
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hgw
  have hspn : (T.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hsp0 : (T.regs 4 - 8#64).toNat = (s.regs 4).toNat - 616 := by rw [BitVec.toNat_sub, hspn]; simp; omega
  -- the base `*Int` (the receiver `z`) at `Mod`/`exp`'s entry memory `sc.mem`
  obtain ⟨-, -, -, -, -, hlive0⟩ := hop 0 (by omega)
  simp only [opAt, Nat.mul_zero, Nat.sub_zero] at hlive0
  have hscr : ∀ o, o + 8 ≤ 32 → sc.mem.readLE ((s.regs 4).toNat - 136 + o) 8 =
      T.mem.readLE ((s.regs 4).toNat - 136 + o) 8 := fun o ho => by
    rw [hscm]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have harrR : 0 < sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8 →
      InRanges (sc.mem.readLE ((s.regs 4).toNat - 136 + 8) 8) (8 * sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8) R.rt :=
    fun hc => by
      rw [hscr 24 (by omega)] at hc; rw [hscr 8 (by omega), hscr 24 (by omega)]; exact (hlive0 hc).2.2.2.2.1
  have harrL : 0 < sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8 →
      ApartAll (sc.mem.readLE ((s.regs 4).toNat - 136 + 8) 8) (8 * sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8) L :=
    fun hc => by
      rw [hscr 24 (by omega)] at hc; rw [hscr 8 (by omega), hscr 24 (by omega)]; exact (hlive0 hc).2.2.2.2.2
  have hgz : Apart RunIface.gA 32 ((s.regs 4).toNat - 136) 32 := by unfold Apart; omega
  have hgaA : 0 < sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8 → Apart RunIface.gA 32
      (sc.mem.readLE ((s.regs 4).toNat - 136 + 8) 8) (8 * sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8) := fun hc =>
    InRanges.apart (harrR hc) hgrt
  -- the result fits `maxW` words: it is below the modulus
  obtain ⟨-, hval2, -, h1282, -, -⟩ := hop 2 (by omega)
  simp only [opAt, natAt, show (s.regs 4).toNat - 136 - 32 * 2 + 8 = (s.regs 4).toNat - 192 by omega,
    show (s.regs 4).toNat - 192 + 8 = (s.regs 4).toNat - 184 by omega,
    show (s.regs 4).toNat - 136 - 32 * 2 + 16 = (s.regs 4).toNat - 184 by omega] at hval2 h1282
  have hlb : RunIface.lenW s'.mem ((s.regs 4).toNat - 136) ≤ RunIface.maxW := by
    obtain ⟨hvz, L', b', -, -, -, hokz, -⟩ := hpost
    have hn := hokz.2.2.2.2.2.2.2.1
    have hlt : natVal s'.mem (s'.mem.readLE ((s.regs 4).toNat - 136 + 8) 8) (s'.mem.readLE ((s.regs 4).toNat - 136 + 16) 8) <
        natVal T.mem (T.mem.readLE ((s.regs 4).toNat - 192) 8) (T.mem.readLE ((s.regs 4).toNat - 184) 8) := by
      have : RunIface.IntV s'.mem ((s.regs 4).toNat - 136) = v := hvz
      unfold RunIface.IntV at this; rw [this, hval2]; exact hvlt
    have := len_le_of_lt_norm _ _ _ _ _ _ hn hlt
    unfold RunIface.lenW RunIface.maxW; omega
  have hBB' : B + RunIface.BytesBudget (RunIface.lenW s'.mem ((s.regs 4).toNat - 136)) ≤ b1 := by
    have : RunIface.BytesBudget (RunIface.lenW s'.mem ((s.regs 4).toNat - 136)) ≤ RunIface.BytesBudget RunIface.maxW := by
      unfold RunIface.BytesBudget allocCost; omega
    omega
  obtain ⟨L2, b2, hext2, hb2, hv1, hinv2, hok2, hMF2, hLF2, hIPb⟩ :=
    afterInt (sp0 := T.regs 4 - 8#64) (g := s.regs 14) (fs := s.fsBase) (M := sc.mem) hIP hpost hsc4 rfl hsc14 hscfs
      hrg hgz hgaA hBB'
  -- `Bytes`' entry memory: the return address `rs2` pushed at `e - 616`
  have hzo := (hIPb { sc with mem := s'.mem } rfl rfl rfl rfl).2.2.2.2.2.1 _ (List.mem_singleton_self _)
  obtain ⟨-, hzw, harw, -⟩ := hzo
  simp only [win, hsc4, hsp0, Janus.outside_cons, Janus.outside_nil, and_true] at hzw harw
  have hpr : ∀ a n, (a + n ≤ (s.regs 4).toNat - 616 ∨ (s.regs 4).toNat - 616 + 8 ≤ a) →
      (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2).readLE a n = s'.mem.readLE a n := fun a n h =>
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ h
  have hlwe : RunIface.lenW (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) =
      RunIface.lenW s'.mem ((s.regs 4).toNat - 136) := hpr _ _ (by omega)
  have hIVe : RunIface.IntV (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) =
      RunIface.IntV s'.mem ((s.regs 4).toNat - 136) := by
    unfold RunIface.IntV
    rw [hpr _ _ (by omega), hpr ((s.regs 4).toNat - 136 + 16) 8 (by omega)]
    by_cases hz : s'.mem.readLE ((s.regs 4).toNat - 136 + 16) 8 = 0
    · rw [hz]; rfl
    · have hc : 0 < s'.mem.readLE ((s.regs 4).toNat - 136 + 24) 8 := by
        have := hok2.2.2.2.2.2.2.1; omega
      have := harw hc
      have hlc := hok2.2.2.2.2.2.2.1
      simp only [natVal]; exact hpr _ _ (by omega)
  have hIPB : ∀ t : State, t.regs 4 = T.regs 4 - 8#64 → t.mem = s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2 →
      t.regs 14 = s.regs 14 → t.fsBase = s.fsBase →
      RunIface.IntPre R b2 (RunIface.BytesBudget (RunIface.lenW (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2)
        ((s.regs 4).toNat - 136))) L2 stkM aboveM [(s.regs 4).toNat - 136] t := by
    intro t h4 hm h14t hfst
    rw [hlwe]
    have h0 := hIPb { t with mem := s'.mem } (by simp only; rw [h4, hsc4]) rfl (by simp only; rw [h14t, hsc14])
      (by simp only; rw [hfst, hscfs])
    exact intPre_push h0 ha8 rs2 rfl rfl rfl (by simp only; rw [hm, h4, hsp0])
  have hxl : RunIface.IntLenLe (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) RunIface.maxW := by
    have h1 := hlwe; have h2 := hlb
    unfold RunIface.lenW at h1 h2; unfold RunIface.IntLenLe; rw [h1]; exact h2
  have hrs : rs2 < 2 ^ 64 := by rcases hpc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hRA : RetAddr ((Extracted.program.onlySegments [RunIface.fnBytes]).link impl)
      ((s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2).readLE (T.regs 4 - 8#64).toNat 8) := by
    rw [hsp0, Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt hrs]
    exact raBytes impl hap rs2 (by rcases hpc' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide)
  have hBy' := bytesW impl hap R stkM aboveM hBy b2 L2 (T.regs 4 - 8#64) (s.regs 14) s.fsBase
    (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) hRA hIPB hxl
  -- facts about `s'` (named before the run shadows it)
  have hMFp : MemFrame s'.mem (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) (R.rt ++ win sc stkM aboveM) := by
    simp only [win, hsc4, hsp0]; janus_frame
  have hz136 : (s.regs 4 - 608#64 + 472#64).toNat = (s.regs 4).toNat - 136 :=
    c2B_sp136 (s.regs 4) (Nat.le_trans (by decide : 608 ≤ 4800) (Nat.le_trans hW1 hb'))
  have hLsL1 : LiveSep L1 (win s W 40) := liveSep_W hext hLs hout hb'
  have hz1 : (s.regs 4).toNat - W ≤ (s.regs 4).toNat - 136 :=
    Nat.sub_le_sub_left (Nat.le_trans (by decide : 136 ≤ 4800) hW1) _
  have hz2 : (s.regs 4).toNat - 136 + 32 ≤ (s.regs 4).toNat + 40 := c2B_le40 _
  -- the frame from `s` to `sc.mem` (the pushed return address of the first call)
  have hMFT : MemFrame s.mem sc.mem (R.rt ++ win s W 40) := by
    refine (memFrame_win hW1 hMF).trans ?_ fun _ _ h => ⟨h, h⟩
    rw [hscm]; simp only [win]; janus_frame
  have hLFT : LiveFrame s.mem sc.mem L [] := by
    refine hLF.trans ?_ fun _ _ h => hext.inRanges_old h
    rw [hscm]; exact LiveFrame.of_win (by simp only [win]; janus_frame) hLsL1
  have hslot : ∀ a, (s.regs 4).toNat - 616 + 144 ≤ a → a + 8 ≤ (s.regs 4).toNat + 40 → Outside a 8 R.rt →
      (a + 8 ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 136 + 32 ≤ a) →
      sc.mem.readLE a 8 = T.mem.readLE a 8 := fun a h1 h2 h3 h4 => by
    rw [hscm]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hDsc : Extracted.program.DataLoaded sc.mem := by
    rw [hscm]
    have hf : MemFrame T.mem (T.mem.writeLE ((s.regs 4).toNat - 616) 8 rs1)
        (R.rt ++ [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by janus_frame
    exact dataLoaded_frame64 hdS (by simp) hro hf fun r hr _ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by dsimp only; omega) (by dsimp only; omega)
  clear hIPB hIPb hIP hBy hpost hop hopA hinv hinv2 hLF hglob0
  have hval : RunIface.IntV (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) = resV s p len :=
    hIVe.trans (hv1.trans hv)
  have hvlt' : RunIface.IntV (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) < opV s p len 2 := by
    rw [hIVe, hv1]; exact hvlt
  have hlb' : RunIface.lenW (s'.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) ≤ RunIface.maxW := by
    rw [hlwe]; exact hlb
  have hRV := fun tB V => relV_of (tB := tB) (V := V) henvW0 hW hW1 hab ha8 hx0 hdf0 hrel0 hscm hsc4 hext2 hb2 hMF2 hLF2
    hrg harrR harrL hval hvlt' hlb' hbfin
  have hacc' : s'.mem.accessible ((s.regs 4).toNat - 616) 8 true = true := by
    rw [hMF2.accessible, hscm, Janus.Arm64.Memory.accessible_writeLE, hMF.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  clear hMF2 hLF2 hIVe hval hvlt' hlb' hlwe hpr hzw harw hok2 hv1 hext2 hb2 hlb hBB' harrR harrL hscr hlive0 hval2 h1282
  rcases hpc' with ⟨hpc1, rfl⟩ | ⟨hpc1, rfl⟩ <;>
  janus64_run [h4', h5', h14', hx', hfs', hdf', hr0', hsp, hsp0, hz136] until [pcCV] calls [hQ := hBy'] <;>
  · obtain ⟨Lk, bk, hR⟩ := hRV _ _ (by janus64_simp [h4']) (by janus64_simp [h5']) (by janus64_simp [h14'])
      (by janus64_simp [hx']) (by janus64_simp [hfs']) (by janus64_simp [hdf']) (by janus64_simp [h4', hsp0]) hQ
    exact hk _ Lk bk (RelV.congr hR rfl rfl rfl rfl (by first | rfl | janus64_simp [hdf'])) (by janus64_simp)

end FvModexp.Amd64.Run
