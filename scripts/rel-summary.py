#!/usr/bin/env python3
"""rel-summary.py SNAPDIR ISA [OUTFILE]: compact verdict table of a verify-all release run (top s47; load column top s50).
Every FAIL and every PASS > 600 s gets the JANUS_TIMINGS split from build/log-<isa>-<row>:
LOAD = host 1-min load average start/end/max over the row (`verify-all-load:` line, verify-all since top s50), LOCK = store/cache-entry lock wait, OWN = janus total - LOCK; own compile (n compiled / from store, s) | kernel replay s | audit s | janus total s (capped rows: last timing line seen)."""
import re, sys, os
snap, isa = sys.argv[1], sys.argv[2]
out = open(sys.argv[3] if len(sys.argv) > 3 else os.path.join(snap, 'rel47-%s.out' % isa)).read()
rows = re.findall(r'^%s\s+(\S+)\s+(PASS|FAIL\S*|MISSING\S*)\s+(\d+)\s+(\d+)' % isa, out, re.M)
npass = sum(1 for r in rows if r[1] == 'PASS')
print('%s: %d rows, %d PASS, %d not PASS' % (isa, len(rows), npass, len(rows) - npass))
for name, v, secs, mb in rows:
    secs = int(secs)
    if v == 'PASS' and secs <= 600: continue
    log = os.path.join(snap, 'build', 'log-%s-%s' % (isa, name))
    t = open(log, errors='ignore').read() if os.path.exists(log) else ''
    oc = re.search(r'own compile \((\d+) compiled, (\d+) from the store\), ok=(\w+)\s+([\d.]+)s', t)
    rp = re.search(r'kernel replay \(closure[^)]*\)\s+([\d.]+)s', t)
    au = re.search(r'theorem audit\s+([\d.]+)s', t)
    to = re.search(r'janus-timing: total\s+([\d.]+)s', t)
    lk = re.search(r'cache entry lock, framework base lease\s+([\d.]+)s', t)
    last = re.findall(r'janus-timing: (.*?)\s+([\d.]+)s', t)
    parts = []
    ld = re.search(r'verify-all-load: start (\S+) end (\S+) max (\S+)', t)
    if ld: parts.append('LOAD %s/%s/%s' % ld.groups())
    if lk: parts.append('LOCK %ss' % round(float(lk.group(1))))
    if lk and to: parts.append('OWN %ss' % round(float(to.group(1)) - float(lk.group(1))))
    if oc: parts.append('compile %s mods %ss ok=%s' % (oc.group(1), round(float(oc.group(4))), oc.group(3)))
    if rp: parts.append('replay %ss' % round(float(rp.group(1))))
    if au: parts.append('audit %ss' % round(float(au.group(1))))
    if to: parts.append('janus %ss' % round(float(to.group(1))))
    elif last: parts.append('last timing: %s %ss' % (last[-1][0][:50], last[-1][1]))
    err = re.findall(r'^(?:error|.*\berror:).*$', t, re.M)
    if v != 'PASS' and err: parts.append('err: ' + err[0][:140])
    print('  %-22s %-8s %4ds %5dMB  %s' % (name, v, secs, int(mb), ' | '.join(parts) or '(no timing lines)'))
loads = []
for name, v, secs, mb in rows:
    log = os.path.join(snap, 'build', 'log-%s-%s' % (isa, name))
    t = open(log, errors='ignore').read() if os.path.exists(log) else ''
    ld = re.search(r'verify-all-load: start (\S+) end (\S+) max (\S+)', t)
    if ld: loads.append(float(ld.group(3)))
if loads:
    print('  host load (max per row): min %.1f, median %.1f, max %.1f over %d rows' % (min(loads), sorted(loads)[len(loads)//2], max(loads), len(loads)))
