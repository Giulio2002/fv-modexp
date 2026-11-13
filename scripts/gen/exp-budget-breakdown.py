# divmc s33: per-term breakdown of Run.Closed.BudOK's left sides (uses exp-budget-check.py; pass --tight via sys.argv edit)
import sys; sys.argv=['x']
import importlib.util
spec=importlib.util.spec_from_file_location('e','/srv/fv-modexp-divmc/scripts/gen/exp-budget-check.py'); e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)
rnd=e.rnd; snc=e.sncN
def nb_parts_at(xl,yl,a0,l,k,bud=True):
    d=dict(mk=e.makeCost(1)+e.makeCost(a0), cR=e.cR(xl,a0)(l), cS_mk=e.makeCost(xl),
      cS_sq=64*yl*e.supSq(128)(l), cS_mul=64*yl*e.supMul(256,xl)(l), cS_div=64*yl*e.supDiv(384,a0)(l),
      cP=e.cP(l,xl,k), win=(e.OBud if bud else e.OCost)(a0,xl,yl,l))
    return d
def argmax_nb(xl,yl,ml,l,k,bud):
    best=None
    for a0 in range(ml+1):
        d=nb_parts_at(xl,yl,a0,l,k,bud); s=sum(d.values())
        if best is None or s>best[0]: best=(s,a0,d)
    return best
def show(xl,yl,n):
    w=max(xl,yl,n); B=(512*yl+128)*e.opCost(w); f=lambda v: '%.3g(%.2g)'%(v,v/B)
    print(f'== (xl,yl,n)=({xl},{yl},{n})  budget B={B:.3g}  [value(ratio to B)]')
    top=dict(mk=e.makeCost(1)+e.makeCost(n), cR=e.cR(xl,n)(0), cS_mk=e.makeCost(xl), cS_sq=64*yl*e.supSq(128)(0),
      cS_mul=64*yl*e.supMul(256,xl)(0), cS_div=64*yl*e.supDiv(384,n)(0), cP=e.cP(0,xl,64*n-1), OBud=e.OBud(n,xl,yl,0), OCost=e.OCost(n,xl,yl,0))
    print(' top:', {k:f(v) for k,v in top.items()})
    ml=n; w2=2*rnd(ml); w3=w2+rnd(2*ml); w4=w3+rnd(2*ml)
    fixed=dict(snc=snc(0,ml)+snc(rnd(ml),ml)+snc(w2,2*ml)+snc(w3,2*ml), mkB=e.makeB(ml+1)*2+e.makeB(ml)+e.makeB(2*ml)+e.alloc(8*(ml+4)),
      costG=e.costG(64*ml), modInv=e.modInv(w4,64*ml), mul2=2*e.mulC(ml,ml)(w4))
    print(' cE fixed:', {k:f(v) for k,v in fixed.items()})
    for L,nm in ((w3,'L3'),(w4,'L4')):
        for bud in (True,False):
            s,a0,d=argmax_nb(xl,yl,ml,L,64*ml,bud)
            print(f' cE {"bU" if bud else "cU"}@{nm}={L} total {f(s)} argmax a0={a0}:', {k:f(v) for k,v in d.items()})
    # window internals at top
    t=23 if yl>1 else 11; k17=17 if yl>1 else 5
    cD=e.divCost(n,xl,0,t); print(' window: cD(divCost)=',f(cD),' snc(2^16,k17 n)=',f(snc(2**16,k17*n)),' cP costO(lm max)=',f(e.costO(0,64*n-1)))
    W=e.W(64*n-1); print(' P2: W=',W,' mulC(W,W)=',f(e.mulC(W,W)(0)),' sqrC(W)=',f(e.sqrC(W)(0)),' rounds w2=32*W,w4=16*W')
for p in [(1,1,1),(1,0,1),(8,8,8),(40,40,40),(64,64,64),(128,0,128),(128,128,128)]: show(*p)
