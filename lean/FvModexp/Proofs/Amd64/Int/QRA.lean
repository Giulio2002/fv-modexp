import FvModexp.Proofs.Amd64.Int.QRDefs

set_option autoImplicit false

/-!
# `(*Int).QuoRem` (amd64), segment A: entry → `nat.div`'s entry (int.go:299-300; `QuoRem+0x0 .. +0x87`)

`q.QuoRem(z, y, z)` from `Mod` (`RSP = t`, `RAX = q`, `RBX = RDI = z`, `RCX = y`): stack check (falls through), `PUSH RBP`,
frame `0x68` (`RSP = t - 112`), the spills of `q, x, y, r` (`t + 8 .. t + 40`), `q.abs` (`= 0`, zeroed by `Mod`),
`r.abs = x.abs = z.abs` (`RSI, R8, R9`), `x.abs` and `y.abs` as stack arguments (`t - 112 .. t - 64`), `RAX = RBX = RCX
= 0`, `RDI = 0` (`stk = nil`), `CALL nat.div` (return `raD`, `RSP = t - 120`). Stops at `nat.div`'s entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runQA (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibQR.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop)
    (t g bp qA zA yA zp zl zc yp yl yc : Nat) (M : Janus.Arm64.Memory) (hbp : bp < 2 ^ 64)
    (ht1 : 128 ≤ t) (ht2 : t + 128 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 120) 160 true = true) (hqacc : M.accessible (t + 96) 32 false = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < t)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 120 ∨ t + 40 ≤ zA)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : M.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 120 ∨ t + 40 ≤ yA)
    (hq : qA = t + 96) (hq8 : M.readLE (qA + 8) 8 = 0) (hq16 : M.readLE (qA + 16) 8 = 0)
    (hq24 : M.readLE (qA + 24) 8 = 0)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz16 : M.readLE (zA + 16) 8 = zl) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hy8 : M.readLE (yA + 8) 8 = yp) (hy16 : M.readLE (yA + 16) 8 = yl) (hy24 : M.readLE (yA + 24) 8 = yc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnQ) (hsp : S.regs 4 = BitVec.ofNat 64 t)
    (h0 : S.regs 0 = BitVec.ofNat 64 qA) (h3 : S.regs 3 = BitVec.ofNat 64 zA) (h1 : S.regs 1 = BitVec.ofNat 64 yA)
    (h7 : S.regs 7 = BitVec.ofNat 64 zA) (h14 : S.regs 14 = BitVec.ofNat 64 g) (h5 : S.regs 5 = BitVec.ofNat 64 bp)
    (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 fnD → S'.regs 4 = BitVec.ofNat 64 (t - 120) →
      S'.regs 0 = 0#64 → S'.regs 3 = 0#64 → S'.regs 1 = 0#64 → S'.regs 7 = 0#64 →
      S'.regs 6 = BitVec.ofNat 64 zp → S'.regs 8 = BitVec.ofNat 64 zl → S'.regs 9 = BitVec.ofNat 64 zc →
      S'.regs 14 = S.regs 14 → S'.regs 5 = BitVec.ofNat 64 (t - 8) → S'.fsBase = S.fsBase → S'.df = S.df →
      S'.mem = M' →
      MemFrame M M' [(t - 120, t - 64), (t - 8, t), (t + 8, t + 40)] → M'.regions = M.regions →
      M'.readLE (t - 120) 8 = raD →
      M'.readLE (t - 112) 8 = zp → M'.readLE (t - 104) 8 = zl → M'.readLE (t - 96) 8 = zc →
      M'.readLE (t - 88) 8 = yp → M'.readLE (t - 80) 8 = yl → M'.readLE (t - 72) 8 = yc →
      M'.readLE (t - 8) 8 = bp → M'.readLE (t + 8) 8 = qA → M'.readLE (t + 16) 8 = zA →
      M'.readLE (t + 24) 8 = yA → M'.readLE (t + 32) 8 = zA →
      Reaches ((LibQR.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibQR.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := hz8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzl : zl < 2 ^ 64 := hz16 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := hy8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := hy16 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := hy24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 t - 8#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) - 104#64 = BitVec.ofNat 64 (t - 112) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (t - 112) - 8#64 = BitVec.ofNat 64 (t - 120) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  subst hq hz8 hz16 hz24 hy8 hy16 hy24 hmem
  janus64_run [hq8, hq16, hq24, es1, es2, es3] until [fnD]
  refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    dsimp only
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (t - 120, t - 64)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (t - 8, t)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (t + 8, t + 40)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals first | omega | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; omega)

end FvModexp.Amd64.IMod
