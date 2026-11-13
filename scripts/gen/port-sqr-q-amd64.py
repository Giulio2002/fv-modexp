# divmc s38: Amd64/Nat/Sqr* (old form) -> Amd64/NatQ/Sqr* (Q-form skeleton; hand edits follow), run from lean/
import re, os
mods = ['SqrDefs','SqrRel','SqrNorm','SqrZero','SqrOne','SqrOneA','SqrCall','SqrMakeR','SqrMakeA1','SqrMakeA2','SqrMakeA',
        'SqrBMP','SqrBM','SqrBS']
qmods = set(mods) | {'BasicSqr'}
D='FvModexp/Proofs/Amd64/NatQ'
files=[]
for m in mods:
    s = open('FvModexp/Proofs/Amd64/Nat/'+m+'.lean').read()
    s = re.sub(r'^import FvModexp\.Proofs\.Amd64\.Nat\.(\w+)', lambda mo: 'import FvModexp.Proofs.Amd64.NatQ.'+mo.group(1) if mo.group(1) in qmods else mo.group(0), s, flags=re.M)
    s = re.sub(r'\bFvModexp\.Amd64\.NatSqr\b', 'FvModexp.Amd64.Q.NatSqr', s)
    if 'autoImplicit false' not in s:
        s = re.sub(r'^(open |namespace )', r'set_option autoImplicit false\n\n\1', s, count=1, flags=re.M)
    s = s.replace('/-!\n# ', '/-!\n# [Q-form copy of Amd64/Nat/'+m+'.lean — TIGHT COSTS, divmc s38] ', 1)
    s = re.sub(r'^(namespace FvModexp\.Amd64\.Q\.NatSqr)\n', r'\1\n\nvariable {H : Nat}\n', s, count=1, flags=re.M)
    f=D+'/'+m+'.lean'; open(f,'w').write(s); files.append(f)
names={'SPre','SPost','KPre','KPost','Core','Pre','Post'}
decl = re.compile(r"^((?:structure|@\[reducible\] def|def|abbrev) ([A-Za-z0-9_']+) \(R : RtInv\) )\(b : Nat\)", re.M)
def argEnd(s, i):
    if s[i] == '(':
        d = 0; j = i
        while True:
            if s[j] == '(': d += 1
            elif s[j] == ')':
                d -= 1
                if d == 0: return j + 1
            j += 1
    mo = re.match(r"[A-Za-z0-9_'.⟨⟩]+", s[i:]); return i + mo.end()
tot=0
for f in files:
    s = open(f).read()
    s = decl.sub(lambda mo: mo.group(1) + '(b H : Nat)', s)
    s = re.sub(r'def (preOf|postOf) \(R : RtInv\) :', r'def \1 (R : RtInv) (H : Nat) :', s)
    s = re.sub(r'\b(preOf|postOf) R (?!H)', r'\1 R H ', s)
    s = s.replace('(R : RtInv) (n : Nat) (j : Mem)', '(R : RtInv) (H n : Nat) (j : Mem)')
    s = re.sub(r'\bIH impl R (?!H)', 'IH impl R H ', s)
    out=[]; i=0
    pat = re.compile(r"(?<![\w.'])((?:BasicSqr\.)?([A-Za-z0-9_']+)) R\s+")
    while True:
        mo = pat.search(s, i)
        if not mo: out.append(s[i:]); break
        nm=mo.group(2); full=mo.group(1)
        ok = nm in names and (nm not in ('Pre','Post') or full.startswith('BasicSqr.'))
        line=s[s.rfind('\n',0,mo.start())+1:mo.start()+200].split('\n')[0].lstrip()
        if ok and not line.startswith(('structure','def','@[','abbrev')):
            j = argEnd(s, mo.end()); out.append(s[i:j]+' H'); i=j; tot+=1
        else:
            out.append(s[i:mo.end()]); i=mo.end()
    s=''.join(out)
    open(f,'w').write(s)
print('apps',tot)
