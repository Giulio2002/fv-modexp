import FvModexp.Proofs.Amd64.Witness.StubsMem
import FvModexp.Proofs.Amd64.Witness.AsmWit
import FvModexp.Proofs.Amd64.Top.RunIface
import Janus.Contracts.PoolSatAmd64

/-!
# Shared witness runtime for the Run extraction (amd64)

amd64 twin of `FvModexp.Arm64.WStubs` (agent asm). One `impl` with a stub at every contract address of the Run
extraction (`build/x-Run-amd64`), and every live contract a row of the Run extraction can assume, proved for the toy
runtime `toyR tys ok` with ANY `tys` (`TysOK`) and ANY `ok` — a witness picks `ok := fun _ _ => True` and gets
`RunIface.Serves` for free (`serves`):

| contract | stub | theorem |
|---|---|---|
| `runtime.memmove` | Janus `MemSatAmd64.memmoveCode` (`REP MOVSB` fwd / `STD; REP MOVSB; CLD` bwd, any size) | `mv` |
| `runtime.memclrNoHeapPointers` | Janus `MemSatAmd64.memclrCode` (`REP STOSB`, any size) | `cl` |
| `runtime.makeslice` / `runtime.newobject` | Janus `LiveSatAmd64.makesliceCodeD` / `newobjectCodeD` | `mk` / `no` |
| `runtime.gcWriteBarrier2/4` | Janus `LiveSatAmd64.wbCode` | `wb2` / `wb4` |
| `sync.(*Pool).Get` / `Put` | Janus `PoolSatAmd64.getCode` (nil) / `putCode` (drop) | `get` / `put` |
| `runtime.growslice` (8-byte `[]Word`) | `Stubs.grCode64` (Go's growth + size classes) | `gr` (`StubsGrow`) |

`hap : ImplApart Extracted.program impl` is proved from the segments' code ranges (`implApart_of_info`), not by a
per-byte `decide` (which takes > 10 min on amd64).
-/

namespace FvModexp.Amd64.WStubs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
open FvModexp.Amd64.Stubs (liveMemRet64_frame)
open Janus.Contracts.LiveSatAmd64 (makesliceCodeD newobjectCodeD wbCode finish_makesliceD finish_newobjectD bump_apart64
  wb_post64)
open Janus.Contracts.MemSatAmd64 (copyB regions_copyB accessible_copyB copyB_bytes_out copyB_bytes copyLE_bytes_out
  copyLE_bytes memFrame_of_bytes fill_frame fill_zeroed fill_ret)

set_option maxRecDepth 100000

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def clA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def noA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wb2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
def wb4A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
def getA : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Get")
def putA : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Put")

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_cl : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = clA := by decide
theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_no : Extracted.program.contractAddr "runtime.newobject" = noA := by decide
theorem addr_wb2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wb2A := by decide
theorem addr_wb4 : Extracted.program.contractAddr "runtime.gcWriteBarrier4" = wb4A := by decide
theorem addr_get : Extracted.program.contractAddr "sync.(*Pool).Get" = getA := by decide
theorem addr_put : Extracted.program.contractAddr "sync.(*Pool).Put" = putA := by decide

/-- The witness runtime's code: one stub per contract address. -/
def impl : List Amd64.Segment :=
  [{ name := "witness.memmove", base := mvA, bytes := MemSatAmd64.memmoveCode },
   { name := "witness.memclr", base := clA, bytes := MemSatAmd64.memclrCode },
   { name := "witness.makeslice", base := mkA, bytes := makesliceCodeD },
   { name := "witness.newobject", base := noA, bytes := newobjectCodeD },
   { name := "witness.wb2", base := wb2A, bytes := wbCode },
   { name := "witness.wb4", base := wb4A, bytes := wbCode },
   { name := "witness.poolget", base := getA, bytes := PoolSatAmd64.getCode },
   { name := "witness.poolput", base := putA, bytes := PoolSatAmd64.putCode }]

/-- `ImplApart` from the code ranges of the extraction (`AsmWit.info_eq`) and of the stubs. -/
theorem implApart_of_info {P : Amd64.Program} {im : List Amd64.Segment} {I : List (Nat × Nat)}
    (hI : AsmWit.info (P.segments ++ im) = I)
    (h1 : I.Pairwise fun a b => a.2 ≤ b.1 ∨ b.2 ≤ a.1)
    (h2 : ∀ a ∈ P.stubs.map (·.addr), ∀ q ∈ I, a < q.1 ∨ q.2 ≤ a) (h3 : ∀ q ∈ I, P.exitAddr < q.1) :
    Amd64.ImplApart P im := by
  subst hI
  refine ⟨?_, fun seg hseg i hi => ?_⟩
  · unfold AsmWit.info at h1
    rw [List.pairwise_map] at h1
    exact h1.imp fun h => by unfold Amd64.Segment.Apart; simpa using h
  · have hq : (seg.base, seg.base + seg.bytes.length) ∈ AsmWit.info (P.segments ++ im) := List.mem_map_of_mem hseg
    refine ⟨?_, ?_⟩
    · unfold Amd64.Program.stubAt
      rw [List.find?_eq_none]
      intro st hst
      have := h2 st.addr (List.mem_map_of_mem hst) _ hq
      simp only [decide_eq_true_eq]
      omega
    · have := h3 _ hq; simp only at this; omega

theorem info_impl : AsmWit.info impl = [(0x48ade0, 0x48ade0 + 34), (0x48aae0, 0x48aae0 + 11), (0x485340, 0x485340 + 28),
    (0x421780, 0x421780 + 24), (0x48a6a0, 0x48a6a0 + 7), (0x48a6e0, 0x48a6e0 + 7), (0x491580, 0x491580 + 5),
    (0x4914c0, 0x4914c0 + 1)] := by decide

theorem hap : ImplApart Extracted.program impl := by
  have hI : AsmWit.info (Extracted.program.segments ++ impl) = AsmWit.infoLit ++ AsmWit.info impl := by
    rw [← AsmWit.info_eq]; simp only [AsmWit.info, List.map_append]
  rw [info_impl] at hI
  exact implApart_of_info hI (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The runtime program the contracts are about. -/
abbrev P : Amd64.Program := Extracted.program.ofImpl impl

/-! ## `memmove`, `memclrNoHeapPointers` -/

set_option maxRecDepth 20000 in
theorem mv (R : RtInv) : MemmoveLive64 P mvA 4096 R := by
  intro L b s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hLm, ⟨hs1, hs2, hs3⟩,
    ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  have hn := (s.regs 1).isLt
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  have hinv := hLm.2.1
  janus64_run until [0x48adf0, 0x48adfe]
  · -- `n = 0`
    refine liveMemRet64_frame (n := 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?gd hinv ?gp
    case gd => have h0 : (s.regs 1).toNat = 0 := (by omega); rw [h0] at hD4; exact hD4
    case gp => intro i hi; omega
    all_goals simp [retAddrOf, setRegF, hdf]
  · -- `dst > src`: backwards
    refine MemSatAmd64.ReachesRet.repMovsbB (c := 0x48adfe) (len := 2) rfl rfl
      ((s.regs 0).toNat + (s.regs 1).toNat - 1) ((s.regs 3).toNat + (s.regs 1).toNat - 1)
      (s.regs 1).toNat rfl
      (by simp [setRegF, BitVec.toNat_sub, BitVec.toNat_add]; omega)
      (by simp [setRegF, BitVec.toNat_sub, BitVec.toNat_add]; omega)
      (by simp [setRegF]) hn (by omega) (by omega)
      (by rw [show (s.regs 0).toNat + (s.regs 1).toNat - 1 + 1 - (s.regs 1).toNat =
            (s.regs 0).toNat by omega]; exact hD2)
      (by rw [show (s.regs 3).toNat + (s.regs 1).toNat - 1 + 1 - (s.regs 1).toNat =
            (s.regs 3).toNat by omega]; exact hs2) ?_
    have hm1 := accessible_copyB s.mem ((s.regs 0).toNat + (s.regs 1).toNat - 1)
      ((s.regs 3).toNat + (s.regs 1).toNat - 1) (s.regs 1).toNat (s.regs 4).toNat 8 false
    have hm2 : (copyB s.mem ((s.regs 0).toNat + (s.regs 1).toNat - 1)
        ((s.regs 3).toNat + (s.regs 1).toNat - 1) (s.regs 1).toNat).readLE (s.regs 4).toNat 8 =
        s.mem.readLE (s.regs 4).toNat 8 :=
      Janus.Arm64.Memory.readLE_congr fun i hi => copyB_bytes_out _ _ _ _ _ (by omega)
    rw [hsp] at hm1
    janus64_run
    refine liveMemRet64_frame ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?gf hD4 hinv ?gp
    case gf => exact memFrame_of_bytes (ws := []) (regions_copyB _ _ _ _) fun x hx => copyB_bytes_out _ _ _ _ _ (by omega)
    case gp =>
      intro i hi
      have h := copyB_bytes s.mem ((s.regs 0).toNat + (s.regs 1).toNat - 1)
        ((s.regs 3).toNat + (s.regs 1).toNat - 1) (s.regs 1).toNat (by omega) (by omega)
        ((s.regs 1).toNat - 1 - i) (by omega)
      rw [show (s.regs 0).toNat + (s.regs 1).toNat - 1 - ((s.regs 1).toNat - 1 - i) =
          (s.regs 0).toNat + i by omega,
        show (s.regs 3).toNat + (s.regs 1).toNat - 1 - ((s.regs 1).toNat - 1 - i) =
          (s.regs 3).toNat + i by omega] at h
      exact h
    all_goals simp [retAddrOf, setRegF, hdf]
  · -- `dst ≤ src`: forwards
    refine MemSatAmd64.ReachesRet.repMovsb (c := 0x48adf0) (len := 2) rfl rfl (s.regs 0).toNat (s.regs 3).toNat
      (s.regs 1).toNat rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) hn hD2 hs2
      (by omega) (by omega) ?_
    have hm1 := accessible_copyLE s.mem (s.regs 0).toNat (s.regs 3).toNat 1 (s.regs 1).toNat
      (s.regs 4).toNat 8 false
    have hm2 : (copyLE s.mem (s.regs 0).toNat (s.regs 3).toNat 1 (s.regs 1).toNat).readLE
        (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
      Janus.Arm64.Memory.readLE_congr fun i hi => copyLE_bytes_out _ _ _ _ _ (by omega)
    rw [hsp] at hm1
    janus64_run
    refine liveMemRet64_frame ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?gf hD4 hinv ?gp
    case gf => exact memFrame_of_bytes (ws := []) (regions_copyLE _ _ _ _ _) fun x hx => copyLE_bytes_out _ _ _ _ _ hx
    case gp => exact copyLE_bytes _ _ _ _ (by omega)
    all_goals simp [retAddrOf, setRegF, hdf]

set_option maxRecDepth 20000 in
theorem cl (R : RtInv) : MemclrNoHeapPointersLive64 P clA 4096 R := by
  intro L b s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hLm, ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  have hm2 := fill_ret (m := s.mem) hD5
  have hm1 : (fillLE s.mem (s.regs 0).toNat 1 0 (s.regs 3).toNat).accessible (s.regs 4).toNat 8
      false = true := by rw [accessible_fillLE]; exact hsp
  have hinv := hLm.2.1
  janus64_run until [0x48aae8]
  refine MemSatAmd64.ReachesRet.repStosb (c := 0x48aae8) (len := 2) rfl rfl (s.regs 0).toNat (s.regs 3).toNat
    rfl (by simp [setRegF]) (by simp [setRegF]) (s.regs 3).isLt hD2 (by omega) ?_
  janus64_run
  refine liveMemRet64_frame ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fill_frame (ws := [])) hD4 hinv (fill_zeroed _ _ _)
  all_goals simp [retAddrOf, setRegF, hdf]

end FvModexp.Amd64.WStubs
