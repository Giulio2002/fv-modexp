import re,sys
MIN0='min (hdrV s p len 0) (len.toNat - 96)'
MST='min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)'
def tr(t):
    t=t.replace('hdrV s p len 1','@@SZ@@')
    t=t.replace(MIN0,'@@MST@@')
    t=t.replace('@@SZ@@','hdrV s p len 2').replace('@@MST@@',MST)
    t=t.replace('ret 2 ','ret @@3 ').replace('ret 1 ','ret 2 ').replace('ret @@3 ','ret 3 ')
    for a,b in [('pcD2','@@pcD3'),('pcD1','pcD2'),('@@pcD3','pcD3'),('pcJ2','pcJ3'),('pcZ2','pcZ3'),
                ('JoinD2','JoinD3'),('JoinZ2','JoinZ3'),('d2join','d3join'),('d2zA','d3zA'),('d2zE','d3zE'),('d2zN','d3zN'),
                ('theorem d2x','theorem d3x'),('theorem d2p','theorem d3p'),('theorem d2l','theorem d3l'),
                ('fn + 0x5cc','fn + 0x6f8'),('fn + 0x608','fn + 0x728'),('fn + 0x64c','fn + 0x750'),('fn + 0x624','fn + 0x730'),
                ('fn + 0x65c','fn + 0x75c'),
                ('s.sp.toNat - 424','@@456'),('s.sp.toNat - 392','s.sp.toNat - 424'),('@@456','s.sp.toNat - 456'),
                ('s.sp - 424','@@456b'),('s.sp - 392','s.sp - 424'),('@@456b','s.sp - 456'),
                ('s.sp - 536','s.sp - 544'),('s.sp.toNat - 536','s.sp.toNat - 544'),
                ('s.sp - 224','s.sp - 232'),('s.sp.toNat - 224','s.sp.toNat - 232'),
                ('s.sp - 256','s.sp - 264'),('s.sp.toNat - 256','s.sp.toNat - 264'),
                ('s.sp.toNat - 160','s.sp.toNat - 192'),('s.sp.toNat - 152','s.sp.toNat - 184'),('s.sp.toNat - 144','s.sp.toNat - 176'),
                ('RunD2ZDefs','RunD3ZDefs'),('Top.RunD2J','Top.RunD3J'),('Top.RunD2Z','Top.RunD3Z'),
                ('hk1, -,','hk1, hk2,'),('hk1 (Nat.le_refl _)','hk1 (by omega)'),
                ('hk1a, hk1b]','hk1a, hk1b, hk2a, hS1, hS1n, hadd, hmod]'),('hk1a, hk1b,','hk1a, hk1b, hk2a, hS1, hS1n, hadd, hmod,')]:
        t=t.replace(a,b)
    t=t.replace('obtain ⟨hk1a, hk1b⟩ := hk1 (by omega)','obtain ⟨hk1a, hk1b⟩ := hk1 (by omega)\n  have hk2a := hk2 (by omega)\n  MODFACTS')
    return t
f,g=sys.argv[1],sys.argv[2]
open(g,'w').write(tr(open(f).read()))
