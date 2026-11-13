# divmc s37: per-term maxima (in units of W = opCost(max xl n)) of the BudOK mirror -> Common/BudQ.Targets.
# usage: python3 exp-budget-terms.py [--bridge] [--qb]   (--bridge: expmc's exp-budget-bridge.py model; --qb: mul/sqr
#   replaced by the PROVED closed bounds of Common/MulCostQB)
import sys, os, importlib.util
import multiprocessing as mp
here = os.path.dirname(os.path.abspath(__file__))
BR = '--bridge' in sys.argv
if not BR: sys.argv.append('--target')
spec = importlib.util.spec_from_file_location('mir', os.path.join(here, 'exp-budget-bridge.py' if BR else 'exp-budget-check.py'))
M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
if '--qb' in sys.argv:
    def mulCB(Mx, n):
        if n < 40: return 16 * Mx + 16 * n + 88
        b = 202 * Mx + 128 * n + 944 if n < 79 else 617 * Mx + 320 * n + 3968
        if Mx < 79: b = min(b, 160 * Mx + 1032)
        elif Mx < 157: b = min(b, 538 * Mx + 4912)
        return b
    def sqrCB(n): return 32 * n + 88 if n < 80 else (128 * n + 808 if n < 158 else 272 * n + 3112)
    M.mulC = lambda x, y: M.TP.const(mulCB(max(x, y), min(x, y)))
    M.sqrC = lambda n: M.TP.const(sqrCB(n))
def res(l, D): return 40 * (4 * (l + D) + 11)
def terms(n):
    out = []
    for xl in range(0, 129, 1 if n <= 8 or n % 16 == 0 else 127):
        cE = M.costE(xl, n); lm = 64 * n - 1
        T = M.cS(xl, n)(0); cp = M.cPv(0, xl, lm)
        for yl in (0, 1, 2, 8, 64, 128):
            W = M.opCost(max(xl, n))
            R = M.cR(xl, n)(0) + (res(0, 17 * xl + 68) if BR else 0)
            S0 = M.makeCost(xl) + (res(0, 64 * max(xl, n) + 128) if BR else 0)
            out.append(dict(xl=xl, yl=yl, n=n, R=R / W, S0=S0 / W, Sy=64 * T / W, E=cE[yl] / W, P=cp[yl] / W,
                            O=max(M.OBud(n, xl, yl, 0), M.OCost(n, xl, yl, 0)) / W,
                            H=(M.stkRes(M.Htop(xl, n)) if M.AMORT else 0) / W, fix=(24 + M.makeCost(1) + M.makeCost(n)) / W))
    return out
if __name__ == '__main__':
    with mp.get_context('fork').Pool(6) as p:
        res_ = sum(p.map(terms, [1, 2, 3, 5, 8, 16, 32, 40, 48, 64, 80, 96, 112, 127, 128]), [])
    for k in ['R', 'S0', 'Sy', 'O', 'H', 'fix']:
        r = max(res_, key=lambda d: d[k]); print(k, round(r[k], 4), (r['xl'], r['yl'], r['n']))
    for k in ['E', 'P']:
        r = max([d for d in res_ if d['yl'] == 0], key=lambda d: d[k]); print(k, '@yl0', round(r[k], 3), (r['xl'], r['yl'], r['n']))
        r = max([d for d in res_ if d['yl'] > 0], key=lambda d: d[k] / d['yl']); print(k, '/yl (incl. yl0 part)', round(r[k] / r['yl'], 3), (r['xl'], r['yl'], r['n']))
