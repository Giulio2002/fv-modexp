#!/usr/bin/env python3
"""stmt-of-thm.py FILE THM K DEFNAME: print `@[reducible] def DEFNAME <first K binders> : Prop := ∀ <rest>, <concl>` built
from the header of `theorem THM` in FILE (divmc s32: continuation statements for flat segment modules, ROW-TIME LESSON)."""
import sys, re
f, thm, k, dn = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
src = open(f).read()
i = src.index(f'theorem {thm} ') + len(f'theorem {thm} ')
j = src.index(':= by', i)
hdr = src[i:j].rstrip()
binders, d, cur, pos = [], 0, '', 0
while pos < len(hdr):
    ch = hdr[pos]
    if d == 0 and ch == ':':
        concl = hdr[pos + 1:].strip(); break
    if ch in '({[⦃': 
        if d == 0: cur = ''
        d += 1
    cur += ch
    if ch in ')}]⦄':
        d -= 1
        if d == 0: binders.append(cur.strip())
    pos += 1
first, rest = binders[:k], binders[k:]
ind = '    '
print(f'@[reducible] def {dn} ' + ' '.join(first) + ' : Prop :=')
print(ind + '∀ ' + ('\n' + ind + '  ').join(' '.join(rest[n:n + 4]) for n in range(0, len(rest), 4)) + ',')
print(ind + '  ' + concl.replace('\n', '\n  '))
