#!/usr/bin/env python3
"""Bottom-up order of the verify-all rows (BRIEF "ROW CAP RULE"): rows share ONE fresh Janus cache, so a row's 15 min / 16 GB cap
must measure its OWN modules; every FvModexp module that another row also needs is compiled by the row lower in the import DAG first.
stdin: one row per line `ID PROOF_FILE` (PROOF_FILE relative to lean/). stdout: one line per row, in run order,
`ID DEP_ID,DEP_ID,...` where DEP_IDs are the rows whose own modules this row imports (directly or not) or with which it shares a
module that the lower row owns. Order: by size of the FvModexp import closure (ties: input order); a row waits for its DEP_IDs.
usage: scripts/row-order.py < rows"""
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
rows = []
for line in sys.stdin:
    f = line.split()
    if len(f) < 2: continue
    mod = f[1][:-5].replace('/', '.') if f[1].endswith('.lean') else f[1]
    rows.append((f[0], mod, closure(mod)))
order = sorted(range(len(rows)), key=lambda i: (len(rows[i][2]), i))
done = []
for i in order:
    rid, mod, cl = rows[i]
    # rows already scheduled that share a non-Spec module with this one (Spec and EthLib are built by the warm-up) run before it
    deps = [rows[j][0] for j in done if any(not m.startswith('FvModexp.Spec') for m in cl & rows[j][2])]
    print(rid, ','.join(deps) if deps else '-')
    done.append(i)
