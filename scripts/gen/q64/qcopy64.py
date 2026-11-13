#!/usr/bin/env python3
"""qcopy.py: Q-form (TIGHT COSTS) copies of asm's division modules (top s38).
usage: qcopy.py plan|copy SEEDFILE MOD...   (MOD = basename in Arm64/Nat, e.g. DivBasicRel)
SEEDFILE: lines `Namespace.name` (short names relative to FvModexp.Amd64) that CHANGE in the Q form (defined by hand
in NatQ/<X>Q*.lean). A candidate module is copied iff it mentions a changed name (incl. names declared by copied
modules), to a fixed point. copy: writes Arm64/NatQ/<MOD>.lean for each copied module (refuses to overwrite), with
namespace FvModexp.Amd64.X -> FvModexp.Amd64.Q.X, `open FvModexp.Amd64.X` after it, imports of copied modules -> NatQ.
"""
import os, re, sys
pkg = "/srv/fv-modexp-top/lean/FvModexp/Proofs/Amd64"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance|opaque)\s+([^\s(:{\[]+)", re.M)
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?.]*")
def src(m): return open(f"{pkg}/Nat/{m}.lean").read()
def nss(t): return re.findall(r"^namespace\s+FvModexp\.Amd64\.(\S+)", t, re.M)
def decls(t):
    ns = nss(t); n0 = ns[0] if ns else ""
    return {(n0, d) for d in DECL.findall(t)}
def mentions(t, ch):
    toks = set(TOK.findall(re.sub(r"--.*", "", re.sub(r"/-.*?-/", "", t, flags=re.S))))
    parts = set()
    for k in toks:
        ps = k.split(".")
        for i in range(len(ps)):
            if i > 0 and not ps[i - 1][:1].isupper(): break
            for j in range(i + 1, len(ps) + 1): parts.add(".".join(ps[i:j]))
    return [c for c in ch if c[1] in parts or f"{c[0]}.{c[1]}" in parts]
def plan(seed, mods):
    ch = set()
    for l in open(seed):
        l = l.strip()
        if l and not l.startswith("#"): a, b = l.split(".", 1); ch.add((a, b))
    cp = set(); why = {}
    while True:
        new = False
        for m in mods:
            if m in cp: continue
            hit = mentions(src(m), ch)
            if hit:
                cp.add(m); why[m] = hit[:3]; ch |= decls(src(m)); new = True
        if not new: break
    return cp, why
DECLB = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|structure)\s+(\S+)(.*?)(?=^(?:@\[|def |abbrev |structure |theorem |lemma |set_option |/--|end |namespace |section ))", re.M | re.S)
def hset(cp, seeds, ns0):
    hs = set(seeds)
    while True:
        new = False
        for m in cp:
            for nm, body in DECLB.findall(src(m)):
                if nm in hs: continue
                if "(b : Nat)" in body.split(":=")[0].split(" where")[0] and any(re.search(r"(?<![\w.])(?:%s\.)?%s R b L\b" % (ns0, re.escape(h)), body) for h in hs):
                    hs.add(nm); new = True
        if not new: return hs
def addH(t, hs, ns0):
    for h in hs:
        t = re.sub(r"(?<![\w.])((?:%s\.)?%s) R b L\b" % (ns0, re.escape(h)), r"\1 R b H L", t)
        t = re.sub(r"^((?:@\[[^\]]*\]\s*)?(?:def|abbrev|structure)\s+%s\s.*?)\(b : Nat\)" % re.escape(h), r"\1(b H : Nat)", t, count=1, flags=re.M | re.S)
    return t
HS = None
def copy(cp):
    for m in sorted(cp):
        dst = f"{pkg}/NatQ/{m}.lean"
        if os.path.exists(dst): print("EXISTS (skip)", dst); continue
        t = src(m)
        for c in cp: t = t.replace(f"import FvModexp.Proofs.Amd64.Nat.{c}\n", f"import FvModexp.Proofs.Amd64.NatQ.{c}\n")
        if HS: t = addH(t, HS, NS0)
        t = re.sub(r"^namespace FvModexp\.Amd64\.(\S+)$", lambda mm: f"namespace FvModexp.Amd64.Q.{mm.group(1)}\nopen FvModexp.Amd64.{mm.group(1)}" + ("" if os.environ.get("NOVAR") else "\nvariable {H : Nat}"), t, flags=re.M)
        t = re.sub(r"^end FvModexp\.Amd64\.(\S+)$", r"end FvModexp.Amd64.Q.\1", t, flags=re.M)
        t = t.replace("/-!\n", f"/-! (Q-form copy of Amd64/Nat/{m}.lean, TIGHT COSTS, top s38)\n", 1)
        if "set_option autoImplicit false" not in t:
            t = re.sub(r"((?:^import .*\n)+)", r"\1\nset_option autoImplicit false\n", t, count=1, flags=re.M)
        open(dst, "w").write(t); print("WROTE", dst)
if __name__ == "__main__":
    cmd, seed, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
    cp, why = plan(seed, mods)
    for m in mods: print(("COPY " if m in cp else "keep ") + m, why.get(m, ""))
    NS0 = os.environ.get("NS0", "DivBasic")
    HS = set() if os.environ.get("NOH") else hset(cp, [l.strip().split(".", 1)[1] for l in open(seed) if l.strip() and not l.startswith("#")], NS0)
    print("H-carrying:", sorted(HS))
    if cmd == "copy": copy(cp)
