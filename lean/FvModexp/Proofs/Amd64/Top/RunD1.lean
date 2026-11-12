import FvModexp.Proofs.Amd64.Top.RunDA0
import FvModexp.Proofs.Amd64.Top.RunDP0
import FvModexp.Proofs.Amd64.Top.RunDM0
import FvModexp.Proofs.Amd64.Top.RunDJS0
import FvModexp.Proofs.Amd64.Top.RunDJF0
import FvModexp.Proofs.Amd64.Top.RunDJZ0

/-! # `Run` (amd64): `C0` to `D1` — the base operand on every path

Direct slice (`dA0`), or the padded buffer: the zeroed stack buffer (`dP0` then `dJS0`) or a fresh `makeslice` buffer
(`dM0` then `dJF0` / `dJZ0` on `dst ≠ src` / `dst = src`), then the `setBytes` segment `dE0`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem d1 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hbud : cstD 3 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.rip = BitVec.ofNat 64 pcC0) (hTm : T.mem = S.mem) (hT4 : T.regs 4 = S.regs 4)
    (hT14 : T.regs 14 = S.regs 14) (hT5 : T.regs 5 = S.regs 5) (hTx : T.xmm 15 = S.xmm 15)
    (hTfs : T.fsBase = S.fsBase) (hTdf : T.df = S.df)
    (hl0 : hdrV s p len 0 ≤ 1024) (hl1 : hdrV s p len 1 ≤ 1024) (hl2 : hdrV s p len 2 ≤ 1024)
    (hnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (hr1 : (T.regs 1).toNat = hdrV s p len 0) (hr13 : (T.regs 13).toNat = hdrV s p len 1)
    (hr0 : (T.regs 0).toNat = hdrV s p len 2) (hr3 : (T.regs 3).toNat = p.toNat + (if 96 < len.toNat then 96 else 0))
    (hr7 : (T.regs 7).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0)) (hr9 : (T.regs 9).toNat = len.toNat - 96)
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 1 1 (cstD 1) L2 b2 S2 → S2.rip = BitVec.ofNat 64 pcD1 →
      (S2.regs 0).toNat = S2.mem.readLE (opAt s 0 + 8) 8 → (S2.regs 3).toNat = S2.mem.readLE (opAt s 0 + 16) 8 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have hE : ∀ S2, AtE R b L c p len cp s ret 0 pcE0 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q :=
    fun S2 ⟨Lk, bk, hrel2, hpc2, h0, h3, h1, hbuf⟩ =>
      dE0 impl hap R hmk hokS b L c p len cp ret hret s hx0 hdf0 henv hin hbud Q S2 Lk bk hrel2 hpc2 h0 h3 h1 hbuf hk
  by_cases hdir : hdrV s p len 0 ≤ len.toNat - 96
  · exact dA0 impl hap R hmk hokS b L c p len cp ret hret s hx0 hdf0 henv hin hbud Q S L1 b1 hrel T hTpc hTm hT4 hT14
      hT5 hTx hTfs hTdf hl0 hl1 hl2 hnz hr1 hr13 hr0 hr3 hr7 hr9 hdir hk
  have hndir : len.toNat - 96 < hdrV s p len 0 := Nat.lt_of_not_le hdir
  by_cases hsm : hdrV s p len 0 ≤ 32
  · exact dP0 impl R b L c p len cp ret hret s hx0 hdf0 henv hin Q S L1 b1 hrel T hTpc hTm hT4 hT14 hT5 hTx hTfs hTdf
      hl0 hl1 hl2 hnz hr1 hr13 hr0 hr3 hr7 hr9 hndir hsm
      fun S2 bk hj hpc h6 h3 h10 h1 h2 h13 =>
        dJS0 impl hap R hmv hokM b L c p len cp ret hret s hx0 hdf0 henv hin Q S2 L1 bk _ hj hsm hpc h6 h3 h10 h1 h2 h13 hE
  · exact dM0 impl hap R hmk hokB b L c p len cp ret hret s hx0 hdf0 henv hin hbud Q S L1 b1 hrel T hTpc hTm hT4 hT14 hT5
      hTx hTfs hTdf hl0 hl1 hl2 hnz hr1 hr13 hr0 hr3 hr7 hr9 hndir (Nat.lt_of_not_le hsm)
      fun S2 bk dst e hj hfr hpc h6 h3 h10 h1 h2 h13 => by
        by_cases heq : dst = p.toNat + inOff len
        · exact dJZ0 impl hap R hmv hokM b L c p len cp ret hret s hx0 hdf0 henv hin Q S2 L1 bk _ dst e hj hfr heq hpc h6 h3
            h10 h1 h2 h13 hE
        · exact dJF0 impl hap R hmv hokM b L c p len cp ret hret s hx0 hdf0 henv hin Q S2 L1 bk _ dst e hj hfr heq hpc h6 h3
            h10 h1 h2 h13 hE

end FvModexp.Amd64.Run
