# divmc s33: numeric mirror of FvModexp.Arm64.Run.Closed.BudOK (Arm64/Top/RunOkRowC.lean) -- NOT a proof.
#   forall xl yl n lm, xl <= 128, yl <= 128, 0 < n <= 128, lm < 64 n:
#     24 + (makeCost 1 + makeCost n + cR 0 xl n + addC cS cE 0 xl yl n + cP 0 xl yl lm + OBud cF n xl yl 0) <= ExpBudget w yl
#     24 + NCost cF cR (addC cS cE) cP xl yl n 0 lm <= ExpBudget w yl            (w = max (max xl yl) n)
# Transcribed from (main 05f3e9d): Common/{Conv,SqrCost,MulCost,StackNatMath,NCostU}, Janus Contracts/Alloc (blockSize),
# Arm64/Nat/{DrsDefs,DivDefs,DivLargeDefs,RemDefs}, Arm64/Exp/{SlowStmt,P2DFull,P2DDefs,P2PreDefs,P2W2,P2W2AT,P2W2LI,
# P2W4,P2W4AT,P2W4LI,W2Fun,W4Fun,W2XnJ,W4XnJ,W2XnS,W4XnS,W2Anc,W4Anc,OddDefs,NDefs,EvE1,EvCost,NFunNE,ModInvDefs,
# SubMod2NDefs,SubMod2NG}, Arm64/Top/RunIface (opCost, ExpBudget).
# Every stack-level (l) dependence is exact: a level-dependent cost is a max of affine functions of l (TP below), all
# slopes >= 0, so supU's maxima over l0 <= l and k0 <= k (costP is monotone in its lm: supTo + makeCost(lm/64+2)) are
# attained at the top; the maximum over the modulus length a0 <= a (NOT monotone) is taken explicitly.
# usage: python3 exp-budget-check.py [--fix]   (--fix: expmc's proposed size-dependent boxes for ExpSlow.cost)
import sys
from functools import lru_cache
import numpy as np
sys.setrecursionlimit(100000)
TIGHT = '--tight' in sys.argv
FIX = '--fix' in sys.argv or TIGHT

# ---- tropical (max-affine) functions of the level l: {slope: intercept}
class TP:
    __slots__ = ('d',)
    def __init__(self, d): self.d = d
    @staticmethod
    def const(c): return TP({0: c})
    def prune(self):
        # drop lines dominated on l in [0, 2^20]: keep line (a,b) unless some (a',b') has a'>=a and b'>=b
        items = sorted(self.d.items(), key=lambda t: (-t[0], -t[1]))
        out = {}; best = -1
        for a, b in items:
            if b > best: out[a] = b; best = b
        self.d = out; return self
    def __add__(self, o):
        if isinstance(o, int): return TP({a: b + o for a, b in self.d.items()})
        r = {}
        for a, b in self.d.items():
            for a2, b2 in o.d.items():
                k = a + a2; v = b + b2
                if r.get(k, -1) < v: r[k] = v
        return TP(r).prune()
    __radd__ = __add__
    def mul(self, c):  # c >= 0 integer
        return TP({a * c: b * c for a, b in self.d.items()}).prune() if c > 0 else TP.const(0)
    def max(self, o):
        r = dict(self.d)
        for a, b in o.d.items():
            if r.get(a, -1) < b: r[a] = b
        return TP(r).prune()
    def shift(self, s):  # l -> l + s
        return TP({a: b + a * s for a, b in self.d.items()})
    def __call__(self, l): return max(a * l + b for a, b in self.d.items())

def tmax(*fs):
    r = fs[0]
    for f in fs[1:]: r = r.max(f)
    return r

alloc = lambda b: 2 * b + 24
makeCap = lambda n: 1 if n == 1 else n + 4
makeCost = lambda n: alloc(8 * makeCap(n))
makeB = lambda k: alloc(8 * (k + 4))
asB = lambda k: alloc(8 * (k + 5))
def sncN(l, n): return alloc(8 * (2 * (l + n + 3) + 4))
def snc(n): return TP({32: 32 * n + 184})          # stackNatCost l n as a function of l
assert all(snc(n)(l) == sncN(l, n) for n in range(5) for l in range(5))
kh = lambda n: (n + 1) // 2
rnd = lambda k: (k + 3) // 4 * 4
sub = lambda a, b: a - b if a > b else 0

SIZE_CLASSES = [8, 16, 24, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240, 256, 288, 320,
   352, 384, 416, 448, 480, 512, 576, 640, 704, 768, 896, 1024, 1152, 1280, 1408, 1536, 1792,
   2048, 2304, 2688, 3072, 3200, 3456, 4096, 4864, 5376, 6144, 6528, 6784, 6912, 8192, 9472,
   9728, 10240, 10880, 12288, 13568, 14336, 16384, 18432, 19072, 20480, 21760, 24576, 27264,
   28672, 32768]
def classSize(n):
    if n == 0: return 0
    for c in SIZE_CLASSES:
        if n <= c: return c
    return n
def roundupsize(size, noscan):
    if size <= 32768 - 8:
        req = size + 8 if (not noscan and size > 512) else size
        return classSize(req) - (req - size)
    return (size + 8192 - 1) // 8192 * 8192
def blockSize(size, noscan=True): return size if (noscan and size < 16) else roundupsize(size, noscan)

# ---- SqrCost
@lru_cache(None)
def ksqrC(n):
    r = snc(2 * n)
    if n >= 80:
        h = (n + 1) // 2
        r = r + (snc(2 * h + 1) + 3 * asB(2 * h + 1) + (ksqrC(h).shift((2 * h + 1 + 3) // 4 * 4) + makeB(2 * h)).mul(3))
    return r
@lru_cache(None)
def sqrC(n): return (ksqrC(n) + makeB(2 * n)) if n >= 12 else TP.const(makeB(2 * n))

# ---- MulCost
@lru_cache(None)
def MC(m, n):
    if n == 0: a = TP.const(0)
    elif n == 1: a = TP.const(makeB(m + 1))
    else:
        if n < 40 or m < n: a = TP.const(makeB(m + n))
        else:
            k = kh(n)
            inner = snc(2 * k + 1) + 4 * asB(2 * k + 1) + MC(k, k).shift(rnd(2 * k + 1)).mul(3)
            if n < m:
                if TIGHT:  # proposal: (m/n - 1) full n x n chunks + one MC(n, m mod n) remainder chunk
                    ch = MC(n, n).shift(rnd(2 * n)).mul(m // n - 1)
                    if m % n: ch = ch + MC(n, m % n).shift(rnd(2 * n))
                    inner = inner + (snc(2 * n) + ch)
                else:
                    inner = inner + (snc(2 * n) + MC(n, n).shift(rnd(2 * n)).mul((m - 1) // n))
            a = inner + makeB(m + n)
    b = None
    if m != 0: b = MC(m - 1, n)
    if n != 0: b = MC(m, n - 1) if b is None else b.max(MC(m, n - 1))
    if b is None: b = TP.const(0)
    return a.max(b)
def mulC(x, y): return MC(max(x, y), min(x, y))

# ---- nat.div / nat.rem
@lru_cache(None)
def drsC(ul, n):
    if n < 40: return snc(n + 1)
    h = n // 2
    s1 = rnd(h + 1)
    body = drsC(ul, n - h + 1).shift(s1) + snc(3 * n).shift(s1) + mulC(h + 1, sub(h, 1)).shift(s1 + rnd(3 * n))
    return snc(h + 1) + body.mul(sub(ul, n) // h + 1)
@lru_cache(None)
def DLc(il, vl):
    return (snc(vl) + makeCost(il + 1) + makeCost(sub(il, vl) + 1) +
            snc(vl + 1).shift(rnd(vl)).max(drsC(il + 1, vl).shift(rnd(vl))))
@lru_cache(None)
def cF(ul, vl): return DLc(ul, vl) + (makeCost(ul) + makeCost(1))
@lru_cache(None)
def cR(ul, vl):
    k = sub(ul, vl) + 1
    return snc(k) + cF(ul, vl).shift(rnd(k))

# ---- expNNSlow
@lru_cache(None)
def supSq(M): return tmax(*[sqrC(n) for n in range(M + 1)])
@lru_cache(None)
def supMul(M, xl): return tmax(*[mulC(n, xl) for n in range(M + 1)])
@lru_cache(None)
def supDiv(M, ml): return tmax(*[cF(n, ml) for n in range(M + 1)])
@lru_cache(None)
def cS(xl, ml):  # returns (makeCost xl, per-yl TP): cS l xl yl ml = makeCost xl + 64*yl*T(l)
    if FIX:
        M = max(xl, ml); T = supSq(M) + supMul(2 * M, xl) + supDiv(3 * M, ml)
    else:
        T = supSq(128) + supMul(256, xl) + supDiv(384, ml)
    return T

# ---- P2 (power-of-two modulus)
W = lambda lm: (lm + 63) // 64
NB = lambda pl, lm: (pl + 1) * W(lm)
tC = lambda lm: makeCost(W(lm) + 4)
def p2pre(l, pl, lm):
    l1 = l + rnd(NB(pl, lm))
    rc = sqrC(W(lm))(l1) + mulC(W(lm), W(lm))(l1) + 2 * tC(lm)
    return sncN(l, NB(pl, lm)) + tC(lm) + sub(pl // 2, 1) * rc
def p2w(l0, lm, wr, pl, rounds, nsq, ntr, yl=None):
    lR = l0 + wr * W(lm); lZ = lR + rnd(2 * W(lm)); lL = lZ + rnd(NB(pl, lm))
    c0 = sncN(l0, wr * W(lm)) + sncN(lR, 2 * W(lm)) + p2pre(lZ, pl, lm)
    bc = nsq * sqrC(W(lm))(lL) + mulC(W(lm), W(lm))(lL) + ntr * tC(lm)
    it = (sub(lm, 2) // 64 + 1) if not TIGHT else min(yl, sub(lm, 2) // 64 + 1)
    return c0 + alloc(8) + 2 * tC(lm) + rounds * it * bc
def costO(l, lm, yl=0): return p2w(l, lm, 8, 4, 32, 2, 3, yl) + p2w(l, lm, 20, 16, 16, 4, 5, yl) + alloc(8)
_supTo = {}
def supToO(l, lm, yl=0):
    key = (l, yl if TIGHT else 0)
    if key not in _supTo:
        arr = []; m = -1
        for j in range(64 * 128 + 1):
            m = max(m, costO(l, j, yl)); arr.append(m)
        _supTo[key] = arr
    return _supTo[key][lm]
def cP(l, xl, lm, yl=0): return supToO(l, lm, yl) + makeCost(xl + 2) + makeCost(lm // 64 + 2)


_cPT = {}
def cPT_table(l):
    """TIGHT: prefix-max table over lm of costO(l, lm, yl) for every yl (int64 [129, 8193])"""
    if l in _cPT: return _cPT[l]
    J = 64 * 128 + 1
    A = np.zeros(J, dtype=np.int64); B = np.zeros(J, dtype=np.int64); Q = np.zeros(J, dtype=np.int64)
    for j in range(J):
        a = alloc(8); b = 0
        for (wr, pl, rounds, nsq, ntr) in ((8, 4, 32, 2, 3), (20, 16, 16, 4, 5)):
            lR = l + wr * W(j); lZ = lR + rnd(2 * W(j)); lL = lZ + rnd(NB(pl, j))
            a += sncN(l, wr * W(j)) + sncN(lR, 2 * W(j)) + p2pre(lZ, pl, j) + alloc(8) + 2 * tC(j)
            b += rounds * (nsq * sqrC(W(j))(lL) + mulC(W(j), W(j))(lL) + ntr * tC(j))
        A[j] = a; B[j] = b; Q[j] = sub(j, 2) // 64 + 1
    T = np.zeros((129, J), dtype=np.int64)
    for yl in range(129):
        T[yl] = np.maximum.accumulate(A + np.minimum(yl, Q) * B)
    _cPT[l] = T; return T
def cPv(l, xl, lm):
    """cP for every yl (object array)"""
    if not TIGHT: return np.full(129, cP(l, xl, lm), dtype=object)
    T = cPT_table(l)
    return np.array([int(T[yl][lm]) for yl in range(129)], dtype=object) + makeCost(xl + 2) + makeCost(lm // 64 + 2)

# ---- windows (expNNOdd)
def xjBud(n, cD, l, k17):
    return (sncN(l, 2 * n) + makeCost(1 + 128 * n // 64 + 1) + sncN(l + rnd(2 * n), 2 * n) + cD + blockSize(8 * n) +
            sncN(l + 2 * rnd(2 * n), k17 * n) + blockSize(8 * (2 * n + 4)))
def xnBudA(n, cD, l0, k, k17):
    return sncN(l0, k) + sncN(l0 + rnd(k), n) + cD + sncN(l0 + rnd(k) + rnd(n), n) + xjBud(n, cD, l0 + rnd(k) + 2 * rnd(n), k17)
def xnBudAC(n, cD, l0, k, k17):
    return sncN(l0, k) + sncN(l0 + rnd(k), n) + cD + xjBud(n, cD, l0 + rnd(k) + rnd(n), k17)
def xjBudA(n, cD, l): return sncN(l, 2 * n) + makeCost(1 + 128 * n // 64 + 1) + sncN(l + rnd(2 * n), 2 * n) + cD
def xnPre(n, cD, l, k):
    AB = sncN(l, k) + sncN(l + rnd(k), n) + cD + sncN(l + rnd(k) + rnd(n), n) + xjBudA(n, cD, l + rnd(k) + 2 * rnd(n))
    AA = sncN(l, k) + sncN(l + rnd(k), n) + cD + xjBudA(n, cD, l + rnd(k) + rnd(n))
    return xjBudA(n, cD, l) + sncN(l, n) + xjBudA(n, cD, l + rnd(n)) + AB + AA
def divCost(n, xl, l, t):
    T = l + rnd(t * n); K = rnd(sub(xl, n) + 1); r = rnd(n); r2 = rnd(2 * n)
    return (cF(xl, n)(T + K + r) + cF(2 * n + 1, n)(T + K + r + r + 2 * r2) + cF(2 * n + 1, n)(T + K + r + 2 * r2) +
            cF(2 * n + 1, n)(T + r + 2 * r2) + cF(2 * n + 1, n)(T + 2 * r2))
def WBud(n, xl, l, t, k17):
    cD = divCost(n, xl, l, t); T = l + rnd(t * n); k = sub(xl, n) + 1
    return (sncN(l, t * n) + xjBud(n, cD, T, k17) + sncN(T, n) + xjBud(n, cD, T + rnd(n), k17) +
            xnBudA(n, cD, T, k, k17) + xnBudAC(n, cD, T, k, k17) + xnPre(n, cD, T, k))
def WCost(n, xl, l, t, k17):
    cD = divCost(n, xl, l, t); T = l + rnd(t * n); k = sub(xl, n) + 1
    return (sncN(l, t * n) + xnPre(n, cD, T, k) + blockSize(8 * n) + sncN((T + 2 * rnd(2 * n)) if TIGHT else 2 ** 16, k17 * n) + blockSize(8 * (2 * n + 4)) +
            makeCost(n))
def OBud(n, xl, yl, l): return WBud(n, xl, l, 23, 17) if 1 < yl else WBud(n, xl, l, 11, 5)
def OCost(n, xl, yl, l): return WCost(n, xl, l, 23, 17) if 1 < yl else WCost(n, xl, l, 11, 5)

# ---- expNNEven
def costG(n):
    return 5 * alloc(8 * (W(n) + 5)) + W(n) * alloc(8 * (2 * W(n) + 2))
def modInv(l, n):
    NW = (n + 63) // 64
    rc = sqrC(NW + 1)(l) + mulC(2 * NW + 2, NW)(l) + 2 * makeCost(2 * NW + 2) + makeCost(NW + 2) + 5 * alloc(8 * (W(n) + 5))
    R = (NW.bit_length() + 1) if TIGHT else NW + 1
    return makeCost(NW + 1) + makeCost(2 * NW) + R * rc

def nb_parts(xl, a0, l, ybig):
    """NBudE / NCost at (xl, a0, l) without cS and cP: returns (budget part, cost part)"""
    base = makeCost(1) + makeCost(a0) + cR(xl, a0)(l)
    yv = 2 if ybig else 0
    return base + OBud(a0, xl, yv, l), base + OCost(a0, xl, yv, l)

YL = np.arange(129, dtype=object)
def supU_vec(xl, ml, l, k):
    """max over a0 <= ml of NBudE / NCost (xl, yl, a0, l, k) for every yl (object arrays over yl)"""
    cp = cPv(l, xl, k)
    bB = None; bC = None
    for a0 in range(ml + 1):
        T = cS(xl, a0)(l)
        for ybig in (False, True):
            pb, pc = nb_parts(xl, a0, l, ybig)
            mask = (YL > 1) if ybig else (YL <= 1)
            vb = np.where(mask, pb + makeCost(xl) + 64 * YL * T + cp, 0)
            vc = np.where(mask, pc + makeCost(xl) + 64 * YL * T + cp, 0)
            bB = vb if bB is None else np.maximum(bB, vb)
            bC = vc if bC is None else np.maximum(bC, vc)
    return bB, bC

def costE(xl, ml):
    """cE 0 xl yl ml for every yl"""
    l0 = 0
    w2 = l0 + rnd(ml) + rnd(ml); w3 = w2 + rnd(2 * ml); w4 = w3 + rnd(2 * ml)
    b3, c3 = supU_vec(xl, ml, w3, 64 * ml)
    b4, c4 = supU_vec(xl, ml, w4, 64 * ml)
    fixed = (sncN(l0, ml) + makeB(ml + 1) + sncN(l0 + rnd(ml), ml) + makeB(ml) + sncN(w2, 2 * ml) + sncN(w3, 2 * ml) +
             alloc(8 * (ml + 4)) + costG(64 * ml) + modInv(w4, 64 * ml) + 2 * mulC(ml, ml)(w4) + makeB(2 * ml) +
             makeB(ml + 1))
    return fixed + b3 + c3 + b4 + c4

opCost = lambda w: alloc(1024 * w + 1024)
ExpBudget = lambda w, yW: ((7 if TIGHT else 8) * (64 * yW) + 128) * opCost(w)

def row(n):
    """[(xl, yl, lhs1, lhs2)] for every xl, yl at modulus length n"""
    out = []
    for xl in range(129):
        cE = costE(xl, n)
        lm = 64 * n - 1
        T = cS(xl, n)(0)
        cs = makeCost(xl) + 64 * YL * T
        cp = cPv(0, xl, lm)
        common = makeCost(1) + makeCost(n) + cR(xl, n)(0) + cs + cE + cp
        for yl in range(129):
            out.append((xl, yl, int(24 + common[yl] + OBud(n, xl, yl, 0)), int(24 + common[yl] + OCost(n, xl, yl, 0))))
    return n, out

def main():
    import multiprocessing as mp, json
    ns = list(range(1, 129))
    if '--quick' in sys.argv: ns = [1, 2, 5, 40, 64, 100, 128]
    res = {}
    with mp.Pool(int(dict(a.split('=') for a in sys.argv[1:] if a.startswith('-j=')).get('-j', 6))) as pool:
        for n, out in pool.imap_unordered(row, ns[::-1]):
            res[n] = out; print('done n', n, flush=True)
    worst = (0,); nbad = 0; fails = []
    for n in sorted(res):
        for xl, yl, l1, l2 in res[n]:
            B = ExpBudget(max(xl, yl, n), yl); r = max(l1, l2) / B
            if r > worst[0]: worst = (r, xl, yl, n, l1, l2, B)
            if max(l1, l2) > B:
                nbad += 1
                if len(fails) < 10: fails.append((xl, yl, n, l1, l2, B))
    print('WORST ratio (lhs/budget)', worst)
    print('#fail', nbad, 'of', sum(len(v) for v in res.values()), 'first', fails)
    out = [a for a in sys.argv[1:] if a.startswith('--out=')]
    if out:
        json.dump({str(n): v for n, v in res.items()}, open(out[0][6:], 'w'))

if __name__ == '__main__':
    main()
