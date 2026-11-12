import FvModexp.Proofs.Amd64.Top.RunCPDefs
import FvModexp.Proofs.Amd64.MemmoveZero

/-! # `Run` (amd64): `P` to the return — `copy(buf[modLen - len(v):], v)` (`memmove`, or skipped)

From `P` (`fn + 0xbf5`): `CX = modLen`, `DX = len(v)`, `SI = buf + ((modLen - len v) masked)`, `DI = len(v)`,
`BX = v`; `CMPQ BX, SI; JE` skips the copy; else `buf` is spilled at `0x190(SP)` (`e - 208`) and
`memmove(SI, BX, DI)` (call `fn + 0xc41`, return `fn + 0xc46`); return `(buf, modLen, modLen)`, `DI = SI = 0`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cp2 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokM : ∀ d sr n, n ≤ 1024 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (W : Nat) (hW : 4800 ≤ W)
    (henv : CallEnv R L s W 40) (Q : Janus.Amd64.Outcome → Prop)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b (okB s p len) L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (U : State) (Lk : List (Nat × Nat)) (bk vp vn buf : Nat) (hj : JoinP R b L p len s ret W Lk bk vp vn buf U)
    (hpc : U.rip = BitVec.ofNat 64 pcP) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hs3, hl2, hsv, hsn, hlt, hr0, hB48, hBacc, hBz, hBL, hBrt, hBsep, hvv,
    hvf, hdS, hext, hbud, hinv, hLsS, hMF, hLF⟩ := hj
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hr0' : U.regs 0 = BitVec.ofNat 64 buf := by rw [← hr0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn5 : (BitVec.ofNat 64 (hdrV s p len 2)).toNat = hdrV s p len 2 := by simp; omega
  have hn1 : (BitVec.ofNat 64 vn).toNat = vn := by simp; omega
  have hs3' : U.mem.readLE ((s.regs 4).toNat - 472) 8 = (BitVec.ofNat 64 (hdrV s p len 2)).toNat := by rw [hs3, hn5]
  have hsn' : U.mem.readLE ((s.regs 4).toNat - 560) 8 = (BitVec.ofNat 64 vn).toNat := by rw [hsn, hn1]
  have hI4 := toInt_small (BitVec.ofNat 64 vn) (by simp; omega)
  have hmask := padMask64 (hdrV s p len 2) vn hlt hl2
  have hlenv := padLen64 (hdrV s p len 2) vn hlt hl2
  obtain ⟨d, hdd⟩ : ∃ d, (if vn = 0 then 0 else hdrV s p len 2 - vn) = d := ⟨_, rfl⟩
  rw [hdd] at hmask
  have hd' : d = 0 ∧ vn = 0 ∨ d + vn = hdrV s p len 2 ∧ 0 < vn := by subst hdd; split <;> omega
  have hda : BitVec.ofNat 64 buf + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + buf) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hvp : vp < 2 ^ 64 := by rw [← hsv]; exact Janus.Arm64.Memory.readLE_lt _ _ 8
  have hsv' : U.mem.readLE ((s.regs 4).toNat - 240) 8 = (BitVec.ofNat 64 vp).toNat := by
    rw [hsv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvp]
  janus64_run [hsp, hm1, hm2, hs3', hsn', hsv', hr0', hI4, hmask, hlenv, hda, BitVec.msb_eq_decide] until
    [segAddr Extracted.program fn + 0xc56, segAddr Extracted.program fn + 0xc33]
  · -- `memmove` skipped: source = destination, only possible for `len(v) = 0`
    sorry
  · sorry

end FvModexp.Amd64.Run
