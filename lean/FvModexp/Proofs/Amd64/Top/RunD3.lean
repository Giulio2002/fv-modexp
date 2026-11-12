import FvModexp.Proofs.Amd64.Top.RunDE2
import FvModexp.Proofs.Amd64.Top.RunDA2
import FvModexp.Proofs.Amd64.Top.RunDP2
import FvModexp.Proofs.Amd64.Top.RunDM2
import FvModexp.Proofs.Amd64.Top.RunDJS2
import FvModexp.Proofs.Amd64.Top.RunDJF2
import FvModexp.Proofs.Amd64.Top.RunDJZ2

/-! # `Run` (amd64): `D2` to `D3` — the modulus operand on every path

Direct slice (`dA2`), or the padded buffer: the zeroed stack buffer (`dP2` then `dJS2`) or a fresh `makeslice` buffer
(`dM2` then `dJF2` / `dJZ2` on `dst ≠ src` / `dst = src`), then the `setBytes` segment `dE2`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem d3 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hbud : cstD 3 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (Lk : List (Nat × Nat)) (bk : Nat) (hrel : RelD R b L c p len cp s ret 2 2 (cstD 2) Lk bk S)
    (hpc : S.rip = BitVec.ofNat 64 pcD2)
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 3 (cstD 3) L2 b2 S2 → S2.rip = BitVec.ofNat 64 pcD3 →
      (S2.regs 0).toNat = S2.mem.readLE (opAt s 2 + 8) 8 → (S2.regs 3).toNat = S2.mem.readLE (opAt s 2 + 16) 8 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  have hE : ∀ S2, AtE R b L c p len cp s ret 2 pcE2 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q :=
    fun S2 ⟨Lk, bk, hrel2, hpc2, h0, h3, h1, hbuf⟩ =>
      dE2 impl hap R hmk hokS b L c p len cp ret hret s hx0 hdf0 henv hin hbud Q S2 Lk bk hrel2 hpc2 h0 h3 h1 hbuf hk
  by_cases hdir : min (hdrV s p len 0 + hdrV s p len 1) (len.toNat - 96) + hdrV s p len 2 ≤ len.toNat - 96
  · exact dA2 impl R b L c p len cp ret hret s hx0 hdf0 henv hin Q S Lk bk hrel hpc hdir hE
  have hndir := Nat.lt_of_not_le hdir
  by_cases hsm : hdrV s p len 2 ≤ 32
  · exact dP2 impl R b L c p len cp ret hret s hx0 hdf0 henv hin Q S Lk bk hrel hpc hndir hsm
      fun S2 bk' src hj hpc2 h0 h3 h2 h1 =>
        dJS2 impl hap R hmv hokM b L c p len cp ret hret s hx0 hdf0 henv hin Q S2 Lk bk' src hj hsm hpc2 h0 h3 h2 h1 hE
  · exact dM2 impl hap R hmk hokB b L c p len cp ret hret s hx0 hdf0 henv hin hbud Q S Lk bk hrel hpc hndir
      (Nat.lt_of_not_le hsm)
      fun S2 bk' dst e src hj hfr hpc2 h0 h3 h2 h1 => by
        by_cases heq : dst = src
        · exact dJZ2 impl hap R hmv hokM b L c p len cp ret hret s hx0 hdf0 henv hin Q S2 Lk bk' src dst e hj hfr heq
            hpc2 h0 h3 h2 h1 hE
        · exact dJF2 impl hap R hmv hokM b L c p len cp ret hret s hx0 hdf0 henv hin Q S2 Lk bk' src dst e hj hfr heq
            hpc2 h0 h3 h2 h1 hE

end FvModexp.Amd64.Run
