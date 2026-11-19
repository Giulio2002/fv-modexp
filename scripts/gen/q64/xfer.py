# transfer single-line arm64 Nat->NatQ changes onto the amd64 NatQ copy when the old line occurs verbatim (stripped)
import sys, re, difflib
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qdiff import norm  # noqa
A64 = __import__("os").path.abspath(__import__("os").path.join(__import__("os").path.dirname(__file__), "../../..")) + "/lean/FvModexp/Proofs/Arm64"; X64 = __import__("os").path.abspath(__import__("os").path.join(__import__("os").path.dirname(__file__), "../../..")) + "/lean/FvModexp/Proofs/Amd64/NatQ"
SKIP = re.compile(r"\s*(import|namespace|end FvModexp|open FvModexp|variable \{H|set_option autoImplicit|/-!)")
for m in sys.argv[1:]:
    try: A = open(f"{A64}/Nat/{m}.lean").read().splitlines(); B = open(f"{A64}/NatQ/{m}.lean").read().splitlines()
    except FileNotFoundError: continue
    p = f"{X64}/{m}.lean"; T = open(p).read().splitlines()
    sm = difflib.SequenceMatcher(None, A, B, autojunk=False); done = 0; left = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal": continue
        olds = [x for x in A[i1:i2] if not SKIP.match(x)]; news = [x for x in B[j1:j2] if not SKIP.match(x)]
        if [norm(x) for x in olds] == [norm(x) for x in news]: continue
        if op == "replace" and len(olds) == len(news):
            for o, n in zip(olds, news):
                if norm(o) == norm(n): continue
                hits = [k for k, x in enumerate(T) if x.strip() == o.strip()]
                hits2 = [k for k, x in enumerate(T) if norm(x) == norm(o)] if not hits else hits
                if hits2:
                    for k in hits2:
                        ind = T[k][:len(T[k]) - len(T[k].lstrip())]; T[k] = ind + n.strip()
                    done += 1
                else: left.append((o, n))
        else: left.append(("\n".join(olds), "\n".join(news)))
    open(p, "w").write("\n".join(T) + "\n")
    print(f"== {m}: transferred {done}, left {len(left)}")
    for o, n in left: print("  < " + o.replace("\n", "\n  < ")[:600]); print("  > " + n.replace("\n", "\n  > ")[:600])
