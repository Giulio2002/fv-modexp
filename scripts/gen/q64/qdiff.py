import sys, re, difflib
def norm(l):
    l = re.sub(r"\bb H\b", "b", l); l = re.sub(r"\bH b\b", "b", l); l = l.replace("(H := H) ", "")
    l = re.sub(r"\bR b L H\b", "R b L", l)
    l = l.replace("NatQ.", "Nat.").replace(".Q.", ".").replace("{H cost W", "{cost W").replace("(H cost", "(cost")
    return l.strip()
def main(a, b):
    A = open(a).read().splitlines(); B = open(b).read().splitlines()
    sm = difflib.SequenceMatcher(None, A, B, autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal": continue
        na = [norm(x) for x in A[i1:i2]]; nb = [norm(x) for x in B[j1:j2]]
        na = [x for x in na if x and not re.match(r"(import|namespace|end FvModexp|open FvModexp|variable \{H|set_option autoImplicit|/-!)", x)]
        nb = [x for x in nb if x and not re.match(r"(import|namespace|end FvModexp|open FvModexp|variable \{H|set_option autoImplicit|/-!)", x)]
        if na == nb: continue
        print(f"@@ {i1+1}-{i2} / {j1+1}-{j2}")
        for x in A[i1:i2]: print("< " + x[:230])
        for x in B[j1:j2]: print("> " + x[:230])
if __name__ == '__main__': main(sys.argv[1], sys.argv[2])
