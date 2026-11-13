import FvModexp.Proofs.Amd64.Int.QRDefs
import FvModexp.Proofs.Common.DivmcMem

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64), segment B: `nat.div`'s return → `QuoRem`'s `RET` (int.go:300-302)

From `raD` (`RSP = t - 112`; `RAX, RBX, RCX` = the quotient, `RDI, RSI, R8` = the remainder): `q.len, q.cap` stored
(`hdrQ`; `q = t + 96` on `Mod`'s frame), the write-barrier flag test (barrier on: `gcWriteBarrier4` at `QuoRem+0xc0`,
callee `RSP = t - 120`, then its 4 buffer stores), `q.ptr`, `r.len, r.cap, r.ptr` into `z`'s header (`r = z`),
`q.neg` (any byte), `r.neg = len r > 0 && x.neg` with `x = z`, `x.neg = 0` (the byte at `z` is still `0`), so `0`
(`finW`); `RAX = q`, epilogue, `RET`. Twin of the arm64 `IMod.runB` (inlined there).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

/-- the memory after `nat.div`'s return: `q.len, q.cap` stored -/
@[reducible] def hdrQ (M : Janus.Arm64.Memory) (qA ql qc : Nat) : Janus.Arm64.Memory :=
  (M.writeLE (qA + 16) 8 ql).writeLE (qA + 24) 8 qc

/-- the final stores after the barrier: `q.ptr`, `z.len, z.cap, z.ptr`, `q.neg = qn`, `z.neg = 0` -/
@[reducible] def finW (Mw : Janus.Arm64.Memory) (qA zA qp r rl rc qn : Nat) : Janus.Arm64.Memory :=
  (((((Mw.writeLE (qA + 8) 8 qp).writeLE (zA + 16) 8 rl).writeLE (zA + 24) 8 rc).writeLE (zA + 8) 8 r).writeLE
    qA 1 qn).writeLE zA 1 0

/-- a store inside the barrier's buffer (runtime-owned, apart from the live set) commutes with `view` -/
theorem view_buf {rt L : List (Nat × Nat)} {buf : Nat} (hR : InRanges buf 32 rt) (hL : ApartAll buf 32 L)
    {a n : Nat} (h1 : buf ≤ a) (h2 : a + n ≤ buf + 32) (M : Janus.Arm64.Memory) (v : Nat) :
    view rt L (M.writeLE a n v) = (view rt L M).writeLE a n v :=
  view_writeLE_vis (hR.sub h1 h2) (Outside.of_sub hL.outside h1 h2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runQB (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibQR.program.link impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    (ret0 : Nat) (hret : RetAddr (LibQR.program.link impl) ret0) (F : State → Prop)
    (t bp qA zA yA qp ql qc r rl rc : Nat) (b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (hal : t % 8 = 0) (ht1 : 4224 ≤ t) (ht2 : t + 128 ≤ 2 ^ 48) (hq : qA = t + 96)
    (hacc : S.mem.accessible (t - 4224) (4224 + 128) true = true)
    (hrt : Outside (t - 4224) (4224 + 128) R.rt) (hLs : LiveSep L1 [(t - 4224, t + 128)])
    (hwbA : S.mem.accessible RunIface.wbA 4 false = true)
    (hwbs : RunIface.wbA + 4 ≤ t - 4224 ∨ t + 128 ≤ RunIface.wbA)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : S.mem.accessible zA 32 true = true) (hzS : zA + 32 ≤ t - 4224 ∨ t + 128 ≤ zA)
    (hzH : Held R L1 zA 32)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : S.mem.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 4224 ∨ t + 128 ≤ yA)
    (hyH : Held R L1 yA 32) (hzy : zA + 32 ≤ yA ∨ yA + 32 ≤ zA)
    (hok : R.ok (cA "runtime.gcWriteBarrier4") [4])
    (hinv : R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 S.mem))
    (hqp : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64) (hr : r < 2 ^ 64) (hrl : rl < 2 ^ 64)
    (hrc : rc < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 raD) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 112))
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h3 : S.regs 3 = BitVec.ofNat 64 ql) (h1 : S.regs 1 = BitVec.ofNat 64 qc)
    (h7 : S.regs 7 = BitVec.ofNat 64 r) (h6 : S.regs 6 = BitVec.ofNat 64 rl) (h8 : S.regs 8 = BitVec.ofNat 64 rc)
    (s8 : S.mem.readLE (t + 8) 8 = qA) (s16 : S.mem.readLE (t + 16) 8 = zA)
    (s24 : S.mem.readLE (t + 24) 8 = yA) (s32 : S.mem.readLE (t + 32) 8 = zA)
    (sbp : S.mem.readLE (t - 8) 8 = bp) (sra : S.mem.readLE t 8 = ret0) (hng : S.mem.readLE zA 1 = 0)
    (KF : ∀ (s4 : State) (Mw : Janus.Arm64.Memory) (qn ql' rl' : Nat),
      s4.mem = finW Mw qA zA qp r rl' rc qn → ql' = ql → rl' = rl →
      MemFrame (hdrQ S.mem qA ql' qc) Mw (R.rt ++ [(t - 4216, t - 112)]) → LiveFrame (hdrQ S.mem qA ql' qc) Mw L1 [] →
      R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 Mw) → s4.regs 4 = BitVec.ofNat 64 (t + 8) →
      s4.regs 0 = BitVec.ofNat 64 qA → s4.regs 14 = S.regs 14 → s4.regs 5 = BitVec.ofNat 64 bp →
      s4.fsBase = S.fsBase → s4.df = S.df → F s4) :
    Reaches ((LibQR.program.link impl).withExit ret0) S (IsReturn F) := by
  have es1 : BitVec.ofNat 64 (t - 112) + 104#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es4 : BitVec.ofNat 64 (t - 112) - 8#64 = BitVec.ofNat 64 (t - 120) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hwbv : RunIface.wbA = 12283968 := rfl
  rw [hwbv] at hwbs hwbA
  subst hq
  have hinv0 : ∀ a c, R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 (hdrQ S.mem (t + 96) a c)) := by
    intro a c; simp only [hdrQ]
    rw [view_writeLE_held (Or.inr (hrt.of_sub (by omega) (by omega))),
      view_writeLE_held (Or.inr (hrt.of_sub (by omega) (by omega)))]
    exact hinv
  have s8' : S.mem.readLE (t - 112 + 120) 8 = t + 96 := by rw [show t - 112 + 120 = t + 8 by omega]; exact s8
  have s16' : S.mem.readLE (t - 112 + 128) 8 = zA := by rw [show t - 112 + 128 = t + 16 by omega]; exact s16
  have s24' : S.mem.readLE (t - 112 + 136) 8 = yA := by rw [show t - 112 + 136 = t + 24 by omega]; exact s24
  have s32' : S.mem.readLE (t - 112 + 144) 8 = zA := by rw [show t - 112 + 144 = t + 32 by omega]; exact s32
  have hLW : LiveSep L1 [(t - 120 - 4096, t - 120 + 8)] := fun r hr => by
    have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hWR : LiveSep [(t - 120 - 4096, t - 120 + 8)] R.rt := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hrt.of_sub (by omega) (by simp only; omega)
  janus64_run [es1, es2, es3, es4, s8', s16', s24', s32', sbp, sra, hng] until [cA "runtime.gcWriteBarrier4"]
  all_goals try refine KF _ _ _ _ _ rfl ?_ ?_ (MemFrame.refl _ _) (LiveFrame.refl _ _ _) (hinv0 _ _) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | rfl | omega | skip
  all_goals
    refine Reaches.call_regions ((hwb L1 b1).withExit hret) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hok, ?_, ?_, ?_⟩
      fun S2 _ hq hrg2 => ?_
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
    · rw [BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_ofNat, Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE,
        Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    · exact RtInv.inv_frame' (ws := [(t - 120, t - 112)]) (by janus_frame)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Or.inl (hrt.of_sub (by simp only; omega) (by simp only; omega))) (hinv0 _ _)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hLW
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hWR
    obtain ⟨buf, f, x, yh, m, zh, kr, rfl, hfr, hlf, hsl, hapL, hapW, hinvS⟩ := hq
    dsimp only at hfr hlf hapW hinvS hsl hapL hrg2
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] at hfr hlf hapW hinvS
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t - 120 < 2 ^ 64 by omega)] at hfr hapW
    obtain ⟨hsl1, hsl2, hsl3, -⟩ := hsl
    have hbufR : InRanges buf.toNat 32 R.rt := by simpa using hsl1
    have hapL' : ApartAll buf.toNat 32 L1 := by simpa using hapL
    have hacc32 : m.accessible buf.toNat 32 true = true := by simpa using hsl3
    have hb8a : m.accessible buf.toNat 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc32 (Nat.le_refl _) (by omega)
    have hb8b : m.accessible (buf.toNat + 8) 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc32 (by omega) (by omega)
    have hb8c : m.accessible (buf.toNat + 16) 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc32 (by omega) (by omega)
    have hb8d : m.accessible (buf.toNat + 24) 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc32 (by omega) (by omega)
    have hbuf64 : buf.toNat + 32 ≤ 2 ^ 48 := by simpa using hsl2
    have hbz : buf.toNat + 32 ≤ zA ∨ zA + 32 ≤ buf.toNat := by
      rcases hzH with hL | hO
      · have := hapL'.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hby : buf.toNat + 32 ≤ yA ∨ yA + 32 ≤ buf.toNat := by
      rcases hyH with hL | hO
      · have := hapL'.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hbS : buf.toNat + 32 ≤ t - 4224 ∨ t + 128 ≤ buf.toNat := by
      have := hbufR.apart hrt; unfold Apart at this; omega
    have hrdS : ∀ a n, t - 112 ≤ a → a + n ≤ t + 128 →
        m.readLE a n = (hdrQ S.mem (t + 96) ql qc).readLE a n := by
      intro a n h1 h2
      rw [hfr.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hrt.of_sub (by omega) (by omega), by omega⟩),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have hrdH : ∀ a n, n ≤ 32 → (a = zA ∨ a = yA) → m.readLE a n = S.mem.readLE a n := by
      intro a n hn ha
      have hH : Held R L1 a 32 := by rcases ha with h | h <;> subst h <;> first | exact hzH | exact hyH
      have hS : a + 32 ≤ t - 4224 ∨ t + 128 ≤ a := by rcases ha with h | h <;> subst h <;> first | exact hzS | exact hyS
      have e : (((S.mem.writeLE (t + 96 + 16) 8 ql).writeLE (t + 96 + 24) 8 qc).writeLE (t - 120) 8 6171653).readLE
          a n = S.mem.readLE a n := by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [← e]
      rcases hH with hL | hO
      · exact hlf.readLE_nil _ _ (hL.sub (by omega) (by omega))
      · exact hfr.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨hO.of_sub (by omega) (by omega), by omega⟩)
    have m1 : m.readLE (t + 96 + 16) 8 = ql := by
      rw [hrdS _ _ (by omega) (by omega)]; simp only [hdrQ]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt hql
    have rdS0 : ∀ a, t - 112 ≤ a → a + 8 ≤ t + 96 → m.readLE a 8 = S.mem.readLE a 8 := by
      intro a h1 h2
      rw [hrdS _ _ (by omega) (by omega)]; simp only [hdrQ]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have m2 : m.readLE (t - 112 + 128) 8 = zA := (rdS0 _ (by omega) (by omega)).trans s16'
    have m3 : m.readLE (t - 112 + 136) 8 = yA := (rdS0 _ (by omega) (by omega)).trans s24'
    have m4 : m.readLE (t - 8) 8 = bp := (rdS0 _ (by omega) (by omega)).trans sbp
    have m5 : m.readLE t 8 = ret0 := (rdS0 _ (by omega) (by omega)).trans sra
    have m9 : m.readLE zA 1 = 0 := (hrdH zA 1 (by omega) (Or.inl rfl)).trans hng
    have m10 : m.readLE yA 1 = S.mem.readLE yA 1 := hrdH yA 1 (by omega) (Or.inr rfl)
    have hmz : m.accessible zA 32 true = true := by
      rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hza
    have hmy : m.accessible yA 32 false = true := by
      rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hya
    have hmS : m.accessible (t - 4224) (4224 + 128) true = true := by
      rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
    have hF1 : MemFrame (hdrQ S.mem (t + 96) ql qc)
        (((S.mem.writeLE (t + 96 + 16) 8 ql).writeLE (t + 96 + 24) 8 qc).writeLE (t - 120) 8 6171653)
        [(t - 120, t - 112)] := by simp only [hdrQ]; janus_frame
    have hfr' : MemFrame (hdrQ S.mem (t + 96) ql qc) m (R.rt ++ [(t - 4216, t - 112)]) :=
      MemFrame.trans hF1 hfr fun a n ho => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨by omega, ho.1, by omega⟩
    have hlf' : LiveFrame (hdrQ S.mem (t + 96) ql qc) m L1 [] := by
      refine ⟨fun a n hin _ => ?_⟩
      rw [hlf.readLE a n hin trivial, hF1.readLE a n ?_]
      obtain ⟨r, hr, h1, h2⟩ := hin
      have h3 := hLW r hr
      simp only [outside_cons, outside_nil, and_true] at h3 ⊢
      omega
    have m6 : m.readLE (t - 120 + 120) 8 = ret0 := by rw [show t - 120 + 120 = t by omega]; exact m5
    have m7 : m.readLE (t - 112 + 104) 8 = bp := by rw [show t - 112 + 104 = t - 8 by omega]; exact m4
    have sra' : S.mem.readLE (t - 120 + 120) 8 = ret0 := by rw [show t - 120 + 120 = t by omega]; exact sra
    have m8 : m.readLE (t - 120 + 136) 8 = zA := by rw [show t - 120 + 136 = t - 112 + 128 by omega]; exact m2
    have m8' : m.readLE (t - 120 + 144) 8 = yA := by rw [show t - 120 + 144 = t - 112 + 136 by omega]; exact m3
    have s16'' : S.mem.readLE (t - 120 + 136) 8 = zA := by rw [show t - 120 + 136 = t + 16 by omega]; exact s16
    have s24'' : S.mem.readLE (t - 120 + 144) 8 = yA := by rw [show t - 120 + 144 = t + 24 by omega]; exact s24
    have es5 : BitVec.ofNat 64 (t - 120) + 8#64 = BitVec.ofNat 64 (t - 112) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    clear hrdS hrdH hfr hlf hsl1 hsl3 hapL rdS0
    janus64_run [hb8a, hb8b, hb8c, hb8d, m1, m2, m3, m4, m5, m6, m7, sra', m8, m8', s16'', s24'', m9, m10, hmz, hmy, hmS, es1, es2, es3, es4, es5]
    all_goals
      refine KF _ _ _ ql _ rfl ?_ ?_ ?mf ?lf ?iv ?_ ?_ ?_ ?_ ?_ ?_
      case mf =>
        repeat (first
          | exact hfr'
          | refine MemFrame.writeLE_inRanges ?_ _ ((hbufR.sub (by omega) (by omega)).append_left _))
      case lf =>
        repeat (first
          | exact hlf'
          | refine LiveFrame.writeLE ?_ _ (Outside.of_sub hapL'.outside (by omega) (by omega)))
      case iv =>
        simp (disch := omega) only [view_buf hbufR hapL']
        exact hinvS _ (by janus_frame)
      all_goals first | omega | (simp only [setRegF_apply, wbRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | rfl


end FvModexp.Amd64.IMod
