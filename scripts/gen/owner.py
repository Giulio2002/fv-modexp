#!/usr/bin/env python3
"""owner.py FILE... -- (agent top) guess each module's owning agent from the prefix of its first commit message
(`asm:`, `divmc:`, `expmc …`, `infra …`, `top:`, …); prints `owner<TAB>file`."""
import sys, subprocess, re
AG = ["asm", "divmc", "expmc", "infra", "top", "mathdiv", "mathexp", "coordinator"]
for f in sys.argv[1:]:
    msgs = subprocess.run(["git", "log", "--format=%s", "--", f], capture_output=True, text=True).stdout.splitlines()
    own = "?"
    for m in reversed(msgs):
        for a in AG:
            if re.match(rf"\W*{a}\b", m, re.I) or re.search(rf"\(agent {a}\b|agent/{a}\b", m):
                own = a; break
        if own != "?": break
    print(f"{own}\t{f}")
