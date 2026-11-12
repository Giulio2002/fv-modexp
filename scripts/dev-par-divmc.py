#!/usr/bin/env python3
"""dev-par-divmc.py ISA FILE.lean...: as dev-deps-infra.py, but compiles the import closure with J (env, default 2)
parallel jobs. Development only (agent divmc; copied from dev-par-expmc.py)."""
import sys, os, re, subprocess, time, tempfile
isa, targets = sys.argv[1], [os.path.realpath(t) for t in sys.argv[2:]]
J = int(os.environ.get('J', '2'))
root = os.path.realpath(os.path.join(os.path.dirname(__file__), '..', 'lean'))
out = os.environ.get("OUT", os.environ.get("DEV", "/srv/fv-modexp-ops/cache-divmc/dev031") + f"/oleans-{isa}")
order, seen, deps = [], set(), {}
def path(mod): return os.path.join(root, *mod.split('.')) + '.lean'
def visit(f):
    if f in seen: return
    seen.add(f)
    deps[f] = [path(m) for m in re.findall(r'^import (\S+)', open(f).read(), re.M) if m.startswith('FvModexp.')]
    for d in deps[f]: visit(d)
    order.append(f)
for t in targets: visit(t)
def olean(f): return os.path.join(out, os.path.relpath(f, root)[:-5] + '.olean')
todo = set()
for f in order:
    ol = olean(f)
    fresh = os.path.exists(ol) and os.path.getmtime(ol) > os.path.getmtime(f) and \
        all(d not in todo and os.path.exists(olean(d)) and os.path.getmtime(olean(d)) <= os.path.getmtime(ol) for d in deps[f])
    if f in targets or not fresh: todo.add(f)
done, running, failed = set(f for f in order if f not in todo), {}, False
while (todo or running) and not failed:
    for f in [f for f in order if f in todo]:
        if len(running) >= J: break
        if all(d in done for d in deps[f]):
            todo.discard(f)
            tf = tempfile.TemporaryFile(mode='w+')  # never a pipe: a full pipe buffer blocks lean (deadlock)
            running[f] = (subprocess.Popen([os.path.join(os.path.dirname(__file__), 'dev-lean-divmc.sh'), '-x', isa, f],
                                           stdout=tf, stderr=subprocess.STDOUT, text=True), tf)
    time.sleep(1)
    for f, (p, tf) in list(running.items()):
        if p.poll() is None: continue
        tf.seek(0); o = tf.read(); tf.close(); del running[f]
        print('\n'.join(l for l in o.splitlines() if l.startswith('==') or 'KB]' in l or 'error' in l)[:3000], flush=True)
        if p.returncode != 0:
            print(o[:8000], flush=True); failed = True
        else: done.add(f)
for f, (p, tf) in running.items():  # failure: let the running jobs finish and still print their output
    p.wait(); tf.seek(0); o = tf.read(); tf.close()
    print(o[:8000], flush=True)
sys.exit(1 if failed else 0)
