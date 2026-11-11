"""(agent top) Generate the amd64 header-2 segments RunH3S/RunH3M/RunH3 from RunH2S/RunH2M/RunH2 (header 1)."""
import re
D='/srv/fv-modexp-top/lean/FvModexp/Proofs/Amd64/Top/'
def R(t,a,b,cnt=None):
    n=t.count(a)
    assert n>0, a
    if cnt is not None: assert n==cnt,(a,n)
    return t.replace(a,b)
def common(t):
    t=R(t,"RelH R b L c p len cp s ret 2 L2 b2 S → S.rip = BitVec.ofNat 64 pcB2 →",
        "RelH R b L c p len cp s ret 3 L2 b2 S → S.rip = BitVec.ofNat 64 pcB3 →\n      (S.regs 0).toNat = S.mem.readLE ((s.regs 4).toNat - 96) 8 → (S.regs 3).toNat = S.mem.readLE ((s.regs 4).toNat - 88) 8 →")
    t=R(t,"(hrel : RelH R b L c p len cp s ret 1 L1 b1 S)","(hrel : RelH R b L c p len cp s ret 2 L1 b1 S)")
    t=R(t,"(hpc : S.rip = BitVec.ofNat 64 pcB1)","(hpc : S.rip = BitVec.ofNat 64 pcB2)")
    t=R(t,"hsl (Nat.le_refl _)","hsl (by omega)")
    t=R(t,"0x65455c","0x65467a")
    t=R(t,"until [pcB2]","until [pcB3]")
    t,k=re.subn(r"\(by janus64_simp\)\n( *)all_goals try \(janus64_simp; done\)",lambda m:"(by janus64_simp) (by janus64_simp) (by janus64_simp)\n"+m.group(1)+"all_goals try (janus64_simp; done)",t)
    assert k==1
    blk0=re.search(r"( *)· refine HdrDone\.transport \(hhd 0 \(by omega\)\).*?all_goals \(simp only \[hdrAt\]; janus64_simp\)\n",t,re.S)
    assert blk0
    t=t[:blk0.end()]+blk0.group(0).replace("hhd 0","hhd 1")+t[blk0.end():]
    t=R(t,"rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl","rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl")
    t=t.replace("rw [hv1, hdrV, Nat.mul_one, padBE_inside _ _ _ _ _ (show 32 + 32 ≤ len.toNat by omega)]","rw [hv1, hdrV, show 32 * 2 = 64 from rfl, padBE_inside _ _ _ _ _ (show 64 + 32 ≤ len.toNat by omega)]")
    t=t.replace("rw [hv1, hdrV, Nat.mul_one]","rw [hv1, hdrV, show 32 * 2 = 64 from rfl]")
    t=t.replace("32 + j","64 + j")
    t=t.replace("- 328","- 360")
    t=t.replace("header 1 = `expLen`: `getData(input, 32, 32)`","header 2 = `modLen`: `getData(input, 64, 32)`")
    t=t.replace("`B1` to `B2`","`B2` to `B3`")
    return t
# H3S
t=open(D+'RunH2S.lean').read()
t=common(t)
t=R(t,"theorem h2s ","theorem h3s ")
t=R(t,"`len < 32`","`len < 64`")
t=R(t,"(h32 : len.toNat < 32) :","(h64 : len.toNat < 64) :")
t=R(t,"  have hc : (len.toNat < len.toNat + 32) = True := by simp\n",
  "  have hc : (len.toNat < len.toNat + 32) = True := by simp\n  have hc64 : (len.toNat < 64) = True := by simp; omega\n  have hl32p : (len + 32#64).toNat = len.toNat + 32 := by rw [BitVec.toNat_add]; simp; omega\n")
t=R(t,"  have hmin : min len.toNat 32 = len.toNat := by omega\n","")
t=t.replace("hmin, hc,","hc, hc64, hl32p,")
t=R(t,"0x1c5","0x2e5")
open(D+'RunH3S.lean','w').write(t)
# H3M
t=open(D+'RunH2M.lean').read()
t=common(t)
t=R(t,"theorem h2m ","theorem h3m ")
t=R(t,"`32 ≤ len < 64`","`64 ≤ len < 96`")
t=R(t,"(h32 : 32 ≤ len.toNat) (h64 : len.toNat < 64) :","(h64 : 64 ≤ len.toNat) (h96 : len.toNat < 96) :")
t=R(t,"  have hc : (len.toNat < 64) = True := by simp; omega\n","  have hc : (len.toNat < 64) = False := by simp; omega\n  have hc96 : (len.toNat < 96) = True := by simp; omega\n")
t=t.replace("hmin, hc,","hmin, hc, hc96,")
t=R(t,"(32#64).toNat < 2 ^ 63","(64#64).toNat < 2 ^ 63")
t=t.replace("neg_asr63_andB cp 32#64","neg_asr63_andB cp 64#64").replace("neg_asr63_andB' cp 32#64","neg_asr63_andB' cp 64#64")
t=t.replace("(if 32 < cp.toNat then 32 else 0)","(if 64 < cp.toNat then 64 else 0)").replace("≤ 32 := by split <;> omega","≤ 64 := by split <;> omega")
t=R(t,"show 32 < cp.toNat","show 64 < cp.toNat")
t=R(t,"have hl32 : (len - 32#64).toNat = len.toNat - 32","have hl32 : (len - 64#64).toNat = len.toNat - 64")
t=t.replace("len.toNat - 32","len.toNat - 64")
t=R(t,"0x1c5","0x2e5")
open(D+'RunH3M.lean','w').write(t)
# H3
t=open(D+'RunH2.lean').read()
t=common(t)
t=R(t,"import FvModexp.Proofs.Amd64.Top.RunH2S\nimport FvModexp.Proofs.Amd64.Top.RunH2M\n","import FvModexp.Proofs.Amd64.Top.RunH3S\nimport FvModexp.Proofs.Amd64.Top.RunH3M\n")
t=R(t,"theorem h2 ","theorem h3 ")
t=R(t,"direct path `64 ≤ len`","direct path `96 ≤ len`")
t=R(t,"""  by_cases h32 : len.toNat < 32
  · exact h2s impl hap R hmk hmv b L c p len cp ret hret s hx0 hdf0 henv hin hokr Q hk S L1 b1 hrel hpc h32
  by_cases h64' : len.toNat < 64
  · exact h2m impl hap R hmk hmv b L c p len cp ret hret s hx0 hdf0 henv hin hokr Q hk S L1 b1 hrel hpc (by omega) h64'
  have h64 : 64 ≤ len.toNat := by omega
""","""  by_cases h64 : len.toNat < 64
  · exact h3s impl hap R hmk hmv b L c p len cp ret hret s hx0 hdf0 henv hin hokr Q hk S L1 b1 hrel hpc h64
  by_cases h96' : len.toNat < 96
  · exact h3m impl hap R hmk hmv b L c p len cp ret hret s hx0 hdf0 henv hin hokr Q hk S L1 b1 hrel hpc (by omega) h96'
  have h96 : 96 ≤ len.toNat := by omega
""")
t=R(t,"  have hc : (len.toNat < 64) = False := by simp; omega\n","  have hc : (len.toNat < 64) = False := by simp; omega\n  have hc96 : (len.toNat < 96) = False := by simp; omega\n")
t=t.replace("hmin, hc,","hmin, hc, hc96,")
t=R(t,"(32#64).toNat < 2 ^ 63","(64#64).toNat < 2 ^ 63")
t=t.replace("neg_asr63_andB cp 32#64","neg_asr63_andB cp 64#64").replace("neg_asr63_andB' cp 32#64","neg_asr63_andB' cp 64#64")
t=R(t,"have hM : (if 32 < cp.toNat then 32 else 0) = 32 := if_pos (show 32 < cp.toNat by omega)","have hM : (if 64 < cp.toNat then 64 else 0) = 64 := if_pos (show 64 < cp.toNat by omega)")
t=R(t,"have hMB : (if (32#64).toNat < cp.toNat then 32#64 else 0#64) = 32#64 := if_pos (show (32#64).toNat < cp.toNat by simp; omega)",
      "have hMB : (if (64#64).toNat < cp.toNat then 64#64 else 0#64) = 64#64 := if_pos (show (64#64).toNat < cp.toNat by simp; omega)")
t=t.replace("(p.toNat + 32) 32","(p.toNat + 64) 32")
t=R(t,"have hp32 : (p + 32#64).toNat = p.toNat + 32","have hp32 : (p + 64#64).toNat = p.toNat + 64")
t=R(t,"have hMB2 : (if 32 < cp.toNat then 32#64 else 0#64) = 32#64 := if_pos (show 32 < cp.toNat by omega)","have hMB2 : (if 64 < cp.toNat then 64#64 else 0#64) = 64#64 := if_pos (show 64 < cp.toNat by omega)")
t=R(t,"try simp only [hMB2, hp32, show (32#64).toNat = 32 from rfl] at hv1","try simp only [hMB2, hp32, show (32#64).toNat = 32 from rfl, show (64#64).toNat = 64 from rfl] at hv1")
open(D+'RunH3.lean','w').write(t)
print("ok")
