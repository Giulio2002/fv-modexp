import re, sys
names = sys.argv[1].split(","); files = sys.argv[2:]
for p in files:
    t = open(p).read(); o = t
    for h in names:
        t = re.sub(r"(?<![\w.])(%s) R b L\b" % re.escape(h), r"\1 R b H L", t)
        t = re.sub(r"^((?:@\[[^\]]*\]\s*)?(?:def|abbrev|structure)\s+%s\s+\(R : RtInv\) )\(b : Nat\)" % re.escape(h), r"\1(b H : Nat)", t, flags=re.M)
    if t != o: open(p, "w").write(t); print("patched", p)
