#!/usr/bin/env python3
"""dev-deps-expmc.py ISA FILE.lean: compile FILE's FvModexp import closure (dependency order, skipping up-to-date
oleans) with scripts/dev-lean-expmc.sh. Development only (agent expmc)."""
import sys, os, re, subprocess
isa, target = sys.argv[1], os.path.realpath(sys.argv[2])
root = os.path.realpath(os.path.join(os.path.dirname(__file__), '..', 'lean'))
out = f"/srv/fv-modexp-ops/cache-expmc/dev/oleans-{isa}"
order, seen = [], set()
def path(mod): return os.path.join(root, *mod.split('.')) + '.lean'
def visit(f):
    if f in seen: return
    seen.add(f)
    for m in re.findall(r'^import (\S+)', open(f).read(), re.M):
        if m.startswith('FvModexp.'): visit(path(m))
    order.append(f)
visit(target)
for f in order:
    rel = os.path.relpath(f, root)[:-5]
    ol = os.path.join(out, rel + '.olean')
    if f != target and os.path.exists(ol) and os.path.getmtime(ol) > os.path.getmtime(f): continue
    r = subprocess.run([os.path.join(os.path.dirname(__file__), 'dev-lean-expmc.sh'), '-x', isa, f], capture_output=True, text=True)
    o = r.stdout + r.stderr
    print('\n'.join(l for l in o.splitlines() if l.startswith('==') or 'KB]' in l or 'error' in l)[:3000])
    if r.returncode != 0:
        print(o[:6000]); sys.exit(1)
