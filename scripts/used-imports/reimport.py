import re,os,sys
ROOT='/srv/fv-modexp-expmc/lean/'
P='FvModexp.Proofs.Arm64.Exp.'
use={}
for l in open('dep.out'):
    m=re.match(r'(\S+): #\[(.*)\]',l)
    if m: use[m.group(1)]=[x.strip() for x in m.group(2).split(',') if x.strip().startswith('FvModexp.')]
def path(m): return ROOT+m.replace('.','/')+'.lean'
def imports(m):
    p=path(m)
    if not os.path.exists(p): return []
    return re.findall(r'^import (\S+)',open(p).read(),re.M)
newimp={}
targets=[m for m in use if m.startswith(P+'W4')]
def cur(m): return newimp.get(m) or imports(m)
clos={}
def closure(m,seen=None):
    # transitive closure under the NEW import graph
    out=set(); st=[m]
    while st:
        x=st.pop()
        for y in cur(x):
            if y not in out: out.add(y); st.append(y)
    return out
for m in targets:
    nonexp=[x for x in imports(m) if not x.startswith(P)]
    exp=[x for x in use[m] if x.startswith(P)]
    newimp[m]=sorted(set(nonexp+exp))
# add missing used other-FvModexp modules
for m in targets:
    c=closure(m)
    for x in use[m]:
        if x not in c and x!=m: newimp[m].append(x); c=closure(m)
# transitive reduction
for m in targets:
    imps=newimp[m]; keep=[]
    for x in imps:
        others=set()
        for y in imps:
            if y!=x: others|=closure(y)|{y}
        if x not in others: keep.append(x)
    newimp[m]=sorted(keep)
changed=0
for m in sorted(targets):
    old=imports(m)
    if sorted(old)!=newimp[m]:
        changed+=1
        print(m[len(P):],':',' '.join(x.replace(P,'') for x in old),' ==> ',' '.join(x.replace(P,'') for x in newimp[m]))
        if len(sys.argv)>1:
            p=path(m); s=open(p).read()
            lines=s.split('\n')
            body=[l for l in lines if not l.startswith('import ')]
            # keep leading position: imports at top
            s2='\n'.join(['import '+x for x in newimp[m]]+body)
            open(p,'w').write(s2)
print('changed',changed)
