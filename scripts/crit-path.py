#!/usr/bin/env python3
"""crit-path.py LOG TARGET.lean [PREFIX]: weighted longest import path (module times from a dev-lean log: '== mod' then
'[t s, …]') over TARGET's FvModexp import closure, restricted to modules whose name starts with PREFIX (default: all
logged). Development only (agent expmc): estimates a row's wall time when its own modules compile along the DAG."""
import sys, os, re
log, target = sys.argv[1], os.path.realpath(sys.argv[2])
root = os.path.realpath(os.path.join(os.path.dirname(__file__), '..', 'lean'))
t, cur = {}, None
for l in open(log):
    m = re.match(r'== (\S+)', l)
    if m: cur = m.group(1)
    m = re.search(r'\[([\d.]+) s,', l)
    if m and cur: t[cur] = float(m.group(1))
deps, seen = {}, set()
def mod(f): return os.path.relpath(f, root)[:-5]
def path(m): return os.path.join(root, *m.split('.')) + '.lean'
def visit(f):
    if f in seen: return
    seen.add(f)
    deps[mod(f)] = [mod(path(m)) for m in re.findall(r'^import (\S+)', open(f).read(), re.M) if m.startswith('FvModexp.')]
    for d in deps[mod(f)]: visit(path(d.replace('/', '.')))
visit(target)
best = {}
def cp(m):
    if m in best: return best[m]
    w = t.get(m, 0.0)
    sub = max([cp(d) for d in deps[m]], key=lambda x: x[0], default=(0.0, []))
    best[m] = (w + sub[0], [(m, w)] + sub[1]); return best[m]
tot, p = cp(mod(target))
print(f"critical path {tot:.0f} s; sum of all logged closure modules {sum(t.get(m,0) for m in deps):.0f} s")
for m, w in p: print(f"  {w:7.1f}  {m}")
