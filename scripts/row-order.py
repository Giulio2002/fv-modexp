#!/usr/bin/env python3
"""Bottom-up order of the verify-all rows (BRIEF "ROW CAP RULE"): rows share ONE fresh Janus cache, so a row's 15 min / 16 GB cap
must measure its OWN modules; every FvModexp module that another row also needs is compiled by the row lower in the import DAG first.
stdin: one row per line `ID PROOF_FILE` (PROOF_FILE relative to lean/). stdout: one line per row, in run order,
`ID DEP_ID,DEP_ID,...` where DEP_IDs are the rows whose own modules this row imports (directly or not) or with which it shares a
module that the lower row owns. Order (coordinator 2026-11-14 "row ORDER for shared closures"): first by the GROUP rank of
GROUPS below (a row's rank = the largest rank of itself and of every row whose proof module lies in its import closure, so a
row never runs before a row it builds on; unlisted leaf rows rank 0), then by size of the FvModexp import closure, then input
order; a row waits for its DEP_IDs.
usage: scripts/row-order.py [--keep-order] < rows   (--keep-order: input order, checked against the import DAG)"""
import os, re, sys
LEAN = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean')
IMP = re.compile(r'^\s*(?:public\s+)?import\s+(FvModexp(?:\.\w+)+)', re.M)
memo = {}
def imports(mod):
    if mod not in memo:
        p = os.path.join(LEAN, *mod.split('.')) + '.lean'
        memo[mod] = IMP.findall(open(p).read()) if os.path.exists(p) else []
    return memo[mod]
def closure(mod):
    seen, todo = set(), [mod]
    while todo:
        m = todo.pop()
        if m in seen: continue
        seen.add(m); todo.extend(imports(m))
    return seen
# (regex on the proof module's last path component, rank), first match wins: StackNat, MulAddWW, BasicMul, BasicSqr, IntAS,
# Sqr, Mul, DivW, DivBasic, Div (incl. DivM / drs / divLarge), Rem, Mod, the exp chain (W2/W4/P2/Even/Slow/ExpN/IExp), Run.
GROUPS = [(r'^StackNat', 1), (r'^MulAddWW', 2), (r'^BasicMul', 3), (r'^BasicSqr', 4), (r'^IntAS', 5),
          (r'^(Nat)?K?Sqr', 6), (r'^(Nat)?K?Mul', 7), (r'^DivW', 8), (r'^DivBasic', 9), (r'^Run', 14),
          (r'^(W2|W4|P2|Even|Slow|ExpN|IExp|Exp|SubMod2N|ModInv)', 13), (r'^(Nat)?Rem', 11),
          (r'^(Nat)?(Div|Drs)', 10), (r'^I?Mod', 12)]
def grank(mod):
    base = mod.split('.')[-1]
    for rx, r in GROUPS:
        if re.match(rx, base): return r
    return 0
rows = []
for line in sys.stdin:
    f = line.split()
    if len(f) < 2: continue
    mod = f[1][:-5].replace('/', '.') if f[1].endswith('.lean') else f[1]
    rows.append((f[0], mod, closure(mod)))
own = {rows[i][1]: grank(rows[i][1]) for i in range(len(rows))}
rank = [max([own[rows[i][1]]] + [own[m] for m in rows[i][2] if m in own]) for i in range(len(rows))]
if '--keep-order' in sys.argv:
    # release order (scripts/release-rows.txt) as given; refuse an order where a row imports the proof module of a LATER row
    order = list(range(len(rows)))
    pos = {rows[i][1]: i for i in order}
    bad = [(rows[i][0], rows[j][0]) for i in order for j in order if j > i and rows[j][1] in rows[i][2]]
    if bad:
        sys.exit('row-order: release order imports a later row: ' + '; '.join(f'{a} imports {b}' for a, b in bad))
else:
    order = sorted(range(len(rows)), key=lambda i: (rank[i], len(rows[i][2]), i))
if '--keep-order' in sys.argv:
    # each shared non-Spec module is OWNED by (charged to) the first row whose closure holds it; a row waits only for the owners
    # of the modules in its closure, so rows of the two ISAs that share only a few Common modules can overlap
    owner = {}
    for i in order:
        rid, mod, cl = rows[i]
        deps = sorted({owner[m] for m in cl if m in owner and not m.startswith('FvModexp.Spec')}, key=lambda j: order.index(j))
        print(rid, ','.join(rows[j][0] for j in deps) if deps else '-')
        for m in cl: owner.setdefault(m, i)
    sys.exit(0)
done = []
for i in order:
    rid, mod, cl = rows[i]
    # rows already scheduled that share a non-Spec module with this one (Spec and EthLib are built by the warm-up) run before it
    deps = [rows[j][0] for j in done if any(not m.startswith('FvModexp.Spec') for m in cl & rows[j][2])]
    print(rid, ','.join(deps) if deps else '-')
    done.append(i)
