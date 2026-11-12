#!/usr/bin/env python3
"""pre-accessors.py SPEC -- (agent top) emit a plain-conjunction `def Pre` and its `Pre.<name>` accessors.
SPEC: python file defining HEAD (def signature up to `:= `), BINDERS (implicit binder text), APP (the applied Pre),
CONJ = [(name, prop), ...]. Prints Lean to stdout."""
import sys
ns = {}
exec(open(sys.argv[1]).read(), ns)
C = ns["CONJ"]
names = ", ".join(n for n, _ in C)
print(f"/-- {ns['DOC']} (conjuncts in order: {names}; accessors `Pre.<name>`). -/")
print(ns["HEAD"])
print(" ∧\n".join(f"  ({p})" for _, p in C))
print()
for i, (n, p) in enumerate(C):
    path = ".2" * i + (".1" if i < len(C) - 1 else "")
    print(f"theorem Pre.{n} {ns['BINDERS']}\n    (h : {ns['APP']}) : {p} := h{path}")
