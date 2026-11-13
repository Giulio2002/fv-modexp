# divmc s37: per-term maxima (in opCost units) of the BudOK mirror -> Common/BudQ.Targets. usage: python3 exp-budget-terms.py [--qb]
import sys, os
sys.argv += ['--target']
import importlib.util
spec = importlib.util.spec_from_file_location('mir', __import__('os').path.join(__import__('os').path.dirname(__file__), 'exp-budget-check.py')); M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
import numpy as np
def terms(n):
    out=[]
    for xl in range(0,129, 1 if n<=8 or n%16==0 else 127):
        cE = M.costE(xl, n); lm = 64*n-1
        T = M.cS(xl, n)(0); cp = M.cPv(0, xl, lm)
        for yl in (0,1,2,8,64,128):
            w = max(xl,yl,n); op = M.opCost(w)
            out.append(dict(xl=xl,yl=yl,n=n, R=M.cR(xl,n)(0)/op, S0=M.makeCost(xl)/op, Sy=64*T/op, E=cE[yl]/op, P=cp[yl]/op,
              O=max(M.OBud(n,xl,yl,0),M.OCost(n,xl,yl,0))/op, H=M.stkRes(M.Htop(xl,n))/op, fix=(24+M.makeCost(1)+M.makeCost(n))/op))
    return out
import multiprocessing as mp
if __name__ != "__main__": raise SystemExit
with mp.get_context("fork").Pool(6) as p: res=sum(p.map(terms, [1,2,3,5,8,16,32,40,48,64,80,96,112,127,128]),[])
for k in ['R','S0','Sy','E','P','O','H','fix']:
    r=max(res,key=lambda d:d[k]); print(k, round(r[k],4), (r['xl'],r['yl'],r['n']))
# yl-slope: E and P per yl
for k in ['E','P']:
    r=max([d for d in res if d['yl']>0],key=lambda d:d[k]/d['yl']); print(k,'/yl', round(r[k]/r['yl'],3), (r['xl'],r['yl'],r['n']))
    r=max([d for d in res if d['yl']==0],key=lambda d:d[k]); print(k,'@yl0', round(r[k],3), (r['xl'],r['yl'],r['n']))
