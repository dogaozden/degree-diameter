import sys
kind = sys.argv[1]; out = sys.argv[2]
if kind == 'D11':   # dihedral of order 22: (r,s) r in Z11, s in Z2; (r1,s1)(r2,s2) = (r1 + (-1)^s1 r2, s1+s2)
    els = [(r, s) for s in range(2) for r in range(11)]
    idx = {e: i for i, e in enumerate(els)}
    def mul(x, y):
        r1, s1 = x; r2, s2 = y
        return ((r1 + (r2 if s1 == 0 else -r2)) % 11, (s1 + s2) % 2)
elif kind == 'F21': # Z7 x| Z3, (a1,b1)(a2,b2) = (a1 + 2^b1 a2 mod 7, b1+b2 mod 3)
    els = [(a, b) for b in range(3) for a in range(7)]
    idx = {e: i for i, e in enumerate(els)}
    def mul(x, y):
        a1, b1 = x; a2, b2 = y
        return ((a1 + pow(2, b1, 7) * a2) % 7, (b1 + b2) % 3)
n = len(els)
ident = [e for e in els if all(mul(e, f) == f for f in els)][0]
assert all(any(mul(x, y) == ident for y in els) for x in els)
assert all(len({mul(x, y) for y in els}) == n for x in els)
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for x in els:
        f.write(" ".join(str(idx[mul(x, y)]) for y in els) + "\n")
print(kind, n, 'identity index', idx[ident])
