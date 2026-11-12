#!/usr/bin/env python3
"""scripts/gen/port-ev-slow.py SRC DST (agent expmc, development helper): mechanical first pass of a port of infra's
nat.expNNEven entry/context modules (frame 336, window sp+448) to nat.expNNSlow (frame 432, window sp+544, seg20).
Numbers are replaced with digit boundaries, simultaneously."""
import sys, re
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
s = s.replace('import FvModexp.Proofs.Arm64.Exp.EvPre', 'import FvModexp.Proofs.Arm64.Exp.SlowDefs')
s = re.sub(r'import FvModexp\.Proofs\.Arm64\.Exp\.Ev(\w+)', lambda m: 'import FvModexp.Proofs.Arm64.Exp.Slow' + {'Ctx': 'Ctx', 'WC': 'WC', 'Stmt': 'Stmt'}.get(m.group(1), m.group(1)), s)
s = s.replace('namespace FvModexp.Arm64.ExpEven', 'namespace FvModexp.Arm64.ExpSlow')
s = s.replace('end FvModexp.Arm64.ExpEven', 'end FvModexp.Arm64.ExpSlow')
s = s.replace('nat.expNNEven', 'nat.expNNSlow').replace('ra_ev', 'ra_slow').replace('seg23', 'seg20')
s = s.replace('0x1b4f70', '0x1b49c0')
num = {'336': '432', '448': '544', '328': '424', '344': '440', '1789808': '1788352', '260': '363'}
s = re.sub(r'(?<![0-9a-zA-Z_.])[0-9]+(?![0-9])', lambda m: num.get(m.group(0), m.group(0)), s)
open(dst, 'w').write(s)
