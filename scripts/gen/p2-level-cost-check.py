# divmc s41: exact transcription of IExp.clP = P2D.cP sqrC mulC (old LEVEL costs; Common/{MulCost,SqrCost,StackNatMath,Conv},
# Exp/{P2DDefs,P2DFull,P2PreDefs,P2W2,P2W4,P2W2AT,P2W4AT,P2W2LI,P2W4LI}) -- shows hp2 (6 W + yl 64 W) is FALSE at n >= 12
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
alloc=lambda b:2*b+24
makeCap=lambda n:1 if n==1 else n+4
makeCost=lambda n:alloc(8*makeCap(n))
makeB=lambda k:alloc(8*(k+4))
asB=lambda k:alloc(8*(k+5))
snc=lambda l,k:alloc(8*(2*(l+k+3)+4))
kh=lambda n:(n+1)//2
rnd=lambda k:(k+3)//4*4
sub=lambda a,b:max(a-b,0)
@lru_cache(None)
def MC(l,m,n):
    if n==0: a=0
    elif n==1: a=makeB(m+1)
    else:
        a=makeB(m+n)
        if not (n<40 or m<n):
            a+=snc(l,2*kh(n)+1)+4*asB(2*kh(n)+1)+3*MC(l+rnd(2*kh(n)+1),kh(n),kh(n))
            if n<m: a+=snc(l,2*n)+(m-1)//n*MC(l+rnd(2*n),n,n)
    b=max(MC(l,m-1,n) if m else 0, MC(l,m,n-1) if n else 0)
    return max(a,b)
mulC=lambda l,x,y:MC(l,max(x,y),min(x,y))
@lru_cache(None)
def ksqrC(l,n):
    r=snc(l,2*n)
    if n>=80:
        h=kh(n); r+=snc(l,2*h+1)+3*asB(2*h+1)+3*(makeB(2*h)+ksqrC(l+rnd(2*h+1),h))
    return r
sqrC=lambda l,n:makeB(2*n)+(ksqrC(l,n) if n>=12 else 0)
W=lambda lm:(lm+63)//64
NB=lambda pl,lm:(pl+1)*W(lm)
tC=lambda lm:makeCost(W(lm)+4)
def pcost(l,pl,lm):
    l1=l+rnd(NB(pl,lm))
    rc=sqrC(l1,W(lm))+mulC(l1,W(lm),W(lm))+2*tC(lm)
    return snc(l,NB(pl,lm))+tC(lm)+(pl//2-1)*rc
def pw(l0,lm,wr,pl,rounds,nsq,ntr,yl):
    lR=l0+wr*W(lm); lZ=lR+rnd(2*W(lm)); lL=lZ+rnd(NB(pl,lm))
    c0=snc(l0,wr*W(lm))+snc(lR,2*W(lm))+pcost(lZ,pl,lm)
    bc=nsq*sqrC(lL,W(lm))+mulC(lL,W(lm),W(lm))+ntr*tC(lm)
    it=min(yl,sub(lm,2)//64+1)
    return c0+alloc(8)+2*tC(lm), rounds*it*bc, rounds*bc
if __name__=='__main__':
    worst0=0; worst1=0
    for w in range(0,129):
        Wd=alloc(1024*max(w,1)+1024)
        lm=64*w
        for lmj in [max(64*w-63,0),64*w]:
            for name,args in (('W2',(8,4,32,2,3)),('W4',(20,16,16,4,5))):
                s,_,per=pw(0,lmj,*args,yl=1)
                r0=(s+alloc(8)+makeCost(2)+makeCost(lmj//64+2))/Wd; r1=per/Wd
                if r0>worst0: worst0=r0; print('setup',name,w,lmj,round(r0,3))
                if r1>worst1: worst1=r1; print('perword',name,w,lmj,round(r1,3))
