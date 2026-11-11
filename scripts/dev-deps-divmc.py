#!/usr/bin/env python3
"""dev-deps-expmc.py ISA FILE.lean: compile FILE's FvModexp import closure (dependency order, skipping up-to-date
oleans) with scripts/dev-lean-divmc.sh. Development only (agent divmc; copied from dev-deps-expmc.py)."""
import sys, os, re, subprocess
isa, target = sys.argv[1], os.path.realpath(sys.argv[2])
root = os.path.realpath(os.path.join(os.path.dirname(__file__), '..', 'lean'))
out = f"/srv/fv-modexp-ops/cache-divmc/dev/oleans-{isa}"
order, seen, deps = [], set(), {}
def path(mod): return os.path.join(root, *mod.split('.')) + '.lean'
def visit(f):
    if f in seen: return
    seen.add(f)
    deps[f] = [path(m) for m in re.findall(r'^import (\S+)', open(f).read(), re.M) if m.startswith('FvModexp.')]
    for d in deps[f]: visit(d)
    order.append(f)
visit(target)
def olean(f): return os.path.join(out, os.path.relpath(f, root)[:-5] + '.olean')
for f in order:
    ol = olean(f)
    fresh = os.path.exists(ol) and os.path.getmtime(ol) > os.path.getmtime(f) and \
        all(os.path.exists(olean(d)) and os.path.getmtime(olean(d)) <= os.path.getmtime(ol) for d in deps[f])
    if f != target and fresh: continue
    r = subprocess.run([os.path.join(os.path.dirname(__file__), 'dev-lean-divmc.sh'), '-x', isa, f], capture_output=True, text=True)
    o = r.stdout + r.stderr
    print('\n'.join(l for l in o.splitlines() if l.startswith('==') or 'KB]' in l or 'error' in l)[:3000])
    if r.returncode != 0:
        print(o[:6000]); sys.exit(1)
