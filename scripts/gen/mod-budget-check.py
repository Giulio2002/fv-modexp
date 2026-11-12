# divmc s30: numeric check of NatDiv.costM DivRec.drsC ul vl <= ModBudget (max ul vl) for ul, vl <= 128 (Python mirror of
# Common/{Conv,SqrCost,MulCost,StackNatMath}, Arm64/Nat/{DrsDefs,DivLargeDefs,DivDefs,DivMDefs}); NOT a proof.
from functools import lru_cache
import sys; sys.setrecursionlimit(100000)
alloc=lambda b: 2*b+24
makeCap=lambda n: 1 if n==1 else n+4
makeCost=lambda n: alloc(8*makeCap(n))
makeB=lambda k: alloc(8*(k+4)); asB=lambda k: alloc(8*(k+5))
snc=lambda l,n: alloc(8*(2*(l+n+3)+4))
kh=lambda n:(n+1)//2; rnd=lambda k:(k+3)//4*4
@lru_cache(None)
def MC(l,m,n):
    if n==0: a=0
    elif n==1: a=makeB(m+1)
    else:
        a=makeB(m+n)
        if not (n<40 or m<n):
            a+= snc(l,2*kh(n)+1)+4*asB(2*kh(n)+1)+3*MC(l+rnd(2*kh(n)+1),kh(n),kh(n))
            if n<m: a+= snc(l,2*n)+(m-1)//n*MC(l+rnd(2*n),n,n)
    b=max(0 if m==0 else MC(l,m-1,n), 0 if n==0 else MC(l,m,n-1))
    return max(a,b)
mulC=lambda l,x,y: MC(l,max(x,y),min(x,y))
@lru_cache(None)
def drsC(l,ul,n):
    if n<40: return snc(l,n+1)
    h=n//2
    return snc(l,h+1)+((ul-n)//h+1)*(drsC(l+rnd(h+1),ul,n-h+1)+snc(l+rnd(h+1),3*n)+mulC(l+rnd(h+1)+rnd(3*n),h+1,max(h-1,0)))
def DL(l,il,vl): return snc(l,vl)+makeCost(il+1)+makeCost(max(il-vl,0)+1)+max(snc(l+rnd(vl),vl+1),drsC(l+rnd(vl),il+1,vl))
def costM(ul,vl): return makeCost(ul)+makeCost(1)+DL(0,ul,vl)+24
opCost=lambda w: alloc(1024*w+1024); MB=lambda w:64*opCost(w)
worst=max(((costM(u,v)/MB(max(u,v)),u,v) for u in range(129) for v in range(129)))
print(worst); bad=[(u,v) for u in range(129) for v in range(129) if costM(u,v)>MB(max(u,v))]; print(len(bad), bad[:5])
