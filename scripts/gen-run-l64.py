"""(agent top) Generate RunLLo/RunLHi (P1 -> C0/error/empty, split on `96 < len`) and the composition RunL (amd64)."""
D='/srv/fv-modexp-top/lean/FvModexp/Proofs/Amd64/Top/'
t=open('/tmp/claude-0/-root/158ba489-000e-4771-a5cb-fabc328941b9/scratchpad/RunL.tmpl').read()
pre=t[:t.index("abbrev pcC0")].replace('import FvModexp.Proofs.Amd64.Top.RunLaDefs','import FvModexp.Proofs.Amd64.Top.RunLDefs')
abbr="abbrev pcC0 : Nat := segAddr Extracted.program fn + 0x5c7\n\n"
thm=t[t.index("set_option maxRecDepth 20000 in\nset_option maxHeartbeats"):t.index("  all_goals trace_state")]
CLOSE = r'''  all_goals first
  | (have hx0 : (T.regs 2).toNat ≤ 64 := by omega
     have hx1 : (T.regs 9).toNat ≤ 64 := by omega
     have hx2 : (T.regs 11).toNat ≤ 64 := by omega
     have hv0 := hU0 hx0
     have hv1 := hU1 hx1
     have hv2 := hU2 hx2
     refine hk _ (by janus64_simp) (by janus64_simp [hTm]) (by janus64_simp [hT4]) (by janus64_simp [hT14])
       (by janus64_simp [hT5]) (by janus64_simp [hTx]) (by janus64_simp [hTfs]) (by janus64_simp [hTdf])
       (by omega) (by omega) (by omega) (by janus64_simp at *; omega) (by janus64_simp; omega) (by janus64_simp; omega)
       (by janus64_simp; omega) ?_ ?_ ?_ <;>
     (janus64_simp <;> (try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]) <;> (try split) <;> omega))
  | (have hx0 : (T.regs 2).toNat ≤ 64 := by omega
     have hx1 : (T.regs 9).toNat ≤ 64 := by omega
     have hx2 : (T.regs 11).toNat ≤ 64 := by omega
     have hv0 := hU0 hx0
     have hv1 := hU1 hx1
     have hv2 := hU2 hx2
     refine hZero _ (by janus64_simp at *; omega) (by omega) (by janus64_simp at *; omega)
       ⟨by janus64_simp [hsp, hT4], by janus64_simp [hm2, regFP], by janus64_simp [h14, hT14, regG],
        by janus64_simp [hx15, hTx]⟩
       (by janus64_simp) (by janus64_simp) ⟨by janus64_simp [hTfs, hfs], by janus64_simp [hTdf, hdf, hdf0], L1, b1, hext,
        by omega, ?_, ?_, ?_⟩
     · dsimp only; (try rw [hTm]); first | exact hinv | exact RtInv.inv_congr hinv rfl (by janus64_simp) rfl
     · dsimp only; (try rw [hTm]); exact hMF
     · dsimp only; (try rw [hTm]); exact hLF)
  | (have hcond : 1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2 := by
       first
       | exact err_of_big hL0' hL1' hL2' (by omega)
       | exact err_of_u hL0' hL1' hL2' (by omega) (by omega)
     rename_i ptr _ _ _ _ m _ _ hLFn hMFn hapL hinR hb48 hacc h8 h16 hz _ hapS hinvn
     have hpo : ptr.toNat + 16 ≤ (s.regs 4).toNat - 4800 ∨ (s.regs 4).toNat + 40 ≤ ptr.toNat := by
       have := InRanges.apart hinR hout; unfold Apart at this; omega
     janus64_run [hm1, hm2]
     refine hErr _ hcond ⟨by janus64_simp [hsp, hT4], by janus64_simp [hm2, regFP], by janus64_simp [h14, hT14, regG],
         by janus64_simp [hx15, hTx]⟩ ⟨by janus64_simp, by janus64_simp, by janus64_simp⟩
       ⟨by janus64_simp [hTfs, hfs], by janus64_simp [hTdf, hdf, hdf0], L1 ++ [(ptr.toNat, ptr.toNat + 16)], b1 - 16, ?_, ?_, ?_, ?_, ?_⟩
     · exact hext.trans (LiveExt.single (by simpa using hinR) (by simpa using hapL))
     · simp only [makeCost, allocCost, makeCap] at hbud hcostE ⊢; omega
     · dsimp only
       have hI : ∀ a, ptr.toNat ≤ a → a + 8 ≤ ptr.toNat + 16 → InRanges a 8 (L1 ++ [(ptr.toNat, ptr.toNat + 16)]) :=
         fun a h1 h2 => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
       first
       | exact inv_store_live (inv_store_live hinvn (hI _ (by omega) (by omega))) (hI _ (Nat.le_refl _) (by omega))
       | exact inv_store_live (inv_store_live hinvn (hI _ (Nat.le_refl _) (by omega))) (hI _ (by omega) (by omega))
     · dsimp only
       refine ⟨fun a n h => ?_, fun a n w => by
         simp only [Janus.Arm64.Memory.accessible_writeLE, hMFn.accessible, hMF.accessible, hTm]⟩
       have h' := h
       simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h'
       have hd1 := InRanges.apart hinR h'.1
       unfold Apart at hd1
       rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
         hMFn.readLE _ _ (by
           simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
           exact ⟨h'.1, by omega, by omega⟩),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
         hMF.readLE _ _ (by
           simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
           exact ⟨h'.1, by omega⟩)]
     · dsimp only
       have ho := hapL.outside
       refine hLF.trans ((((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans hLFn (fun _ _ h => h)).writeLE _
         (ho.of_sub (by omega) (by omega))).writeLE _ (ho.of_sub (Nat.le_refl _) (by omega))) (fun _ _ h => hext.inRanges_old h))
'''
for nm,cond,doc in [("lbLo","(h96 : len.toNat ≤ 96)","`len ≤ 96`"),("lbHi","(h96 : 96 < len.toNat)","`96 < len`")]:
    th=thm.replace("theorem lb (","theorem "+nm+" (").replace("(hrecv : s.mem.readLE c.toNat 3 = 65793)","(hrecv : s.mem.readLE c.toNat 3 = 65793) "+cond)
    th=th.replace("  have hLs0 := hLsS\n","")
    th=th.replace("  obtain ⟨hcacc,","  have hLsL1 : LiveSep L1 (win s 4800 40) := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1\n  obtain ⟨hcacc,",1)
    body=pre.replace("/-! # `Run` (amd64): `P1` to `C0`","/-! # `Run` (amd64): `P1` to `C0`, "+doc+" —")+"namespace FvModexp.Amd64.Run\n\n"+th+CLOSE+"\nend FvModexp.Amd64.Run\n"
    body=body.replace("namespace FvModexp.Amd64.Run\n\nnamespace FvModexp.Amd64.Run","namespace FvModexp.Amd64.Run")
    open(D+('RunLLo.lean' if nm=='lbLo' else 'RunLHi.lean'),'w').write(body)
