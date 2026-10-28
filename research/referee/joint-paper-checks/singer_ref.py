"""Referee check of Section 4.3 (cyclic model of W(3,q), q odd prime): Proposition 4.10, the remark after it
(general delta_0), the spread {yK}, and the graph of Corollary 4.11 with its regular completion."""
import itertools, sys
def irreducible_quartic(p):
    # find monic x^4 + c3 x^3 + c2 x^2 + c1 x + c0 with no roots and no quadratic factor
    polys2 = [(a, b) for a in range(p) for b in range(p)]  # x^2+a x+b
    def mulpoly(A, B):
        r = [0] * (len(A) + len(B) - 1)
        for i, x in enumerate(A):
            for j, y in enumerate(B): r[i + j] = (r[i + j] + x * y) % p
        return r
    quads = set()
    for (a, b) in polys2:
        for (c, d) in polys2:
            quads.add(tuple(mulpoly([b, a, 1], [d, c, 1])))
    for c in itertools.product(range(p), repeat=4):
        f = list(c) + [1]
        if any(sum(f[i] * pow(x, i, p) for i in range(5)) % p == 0 for x in range(p)): continue
        if tuple(f) in quads: continue
        return f
class E4:
    def __init__(self, p):
        self.p = p; f = irreducible_quartic(p); self.f = f
        self.q4 = p ** 4
        # elements as ints base p (4 digits)
        def mul(a, b):
            va = [(a // p**i) % p for i in range(4)]; vb = [(b // p**i) % p for i in range(4)]
            r = [0] * 7
            for i in range(4):
                for j in range(4): r[i + j] = (r[i + j] + va[i] * vb[j]) % p
            for k in range(6, 3, -1):
                c = r[k]
                if c:
                    r[k] = 0
                    for i in range(4): r[k - 4 + i] = (r[k - 4 + i] - c * f[i]) % p
            return sum(r[i] * p**i for i in range(4))
        self.mulf = mul
        for g in range(2, self.q4):
            x, cnt = 1, 0
            while True:
                x = mul(x, g); cnt += 1
                if x == 1: break
            if cnt == self.q4 - 1: self.g = g; break
        self.exp = [1]
        for _ in range(self.q4 - 2): self.exp.append(mul(self.exp[-1], self.g))
        self.log = {v: i for i, v in enumerate(self.exp)}
    def add(self, a, b):
        p = self.p
        return sum(((a // p**i + b // p**i) % p) * p**i for i in range(4))
    def smul(self, s, a):  # scalar in F_p
        p = self.p
        return sum(((s * (a // p**i)) % p) * p**i for i in range(4))
    def mul(self, a, b):
        if a == 0 or b == 0: return 0
        return self.exp[(self.log[a] + self.log[b]) % (self.q4 - 1)]
    def pw(self, a, n):
        if a == 0: return 0
        return self.exp[(self.log[a] * n) % (self.q4 - 1)]
    def tr(self, a):  # Tr_{E/F_p}
        q = self.p; t = 0; x = a
        for _ in range(4): t = self.add(t, x); x = self.pw(x, q)
        assert t < q
        return t
def run(q):
    E = E4(q); Q4 = q**4; n = (q + 1) * (q * q + 1); g = E.g
    d = E.exp[(q * q + 1) // 2]; dbar = E.pw(d, q * q); assert dbar == E.smul(q - 1, d)
    h = E.exp[q * q + 1]
    def b(delta, y, z):
        return E.tr(E.mul(delta, E.mul(y, E.pw(z, q * q))))
    pidx = lambda v: E.log[v] % n
    # all lines of PG(3,q) as frozensets of point indices
    lines = {}
    for i in range(n):
        for j in range(i + 1, n):
            y, z = E.exp[i], E.exp[j]
            key = None
            pts = {i, j} | {pidx(E.add(E.smul(s, y), z)) for s in range(q)}
            fs = frozenset(pts)
            if fs not in lines: lines[fs] = (y, z)
    assert len(lines) == (q*q + 1) * (q*q + q + 1)
    cls = lambda i: i % (q + 1)
    # (a)
    worst = max(max(sum(1 for i in L if cls(i) == a) for a in range(q + 1)) for L in lines)
    ti = [L for L, (y, z) in lines.items() if b(d, y, z) == 0]
    assert len(ti) == (q + 1) * (q*q + 1)
    good = []
    for a in range(q + 1):
        for c in range(a + 1, q + 1):
            if all(sum(1 for i in L if cls(i) in (a, c)) == 2 for L in ti): good.append((a, c))
    print(f"q={q}: lines of PG(3,q) meet a class in at most {worst} points; t.i. lines {len(ti)}; pairs (a,c) giving 2-ovoids: {good};"
          f" expected {{a,q-a}}: {sorted(tuple(sorted((a, q - a))) for a in range((q + 1)//2))}")
    # spread {yK}: K* = <h>; line yK = points g^{i+(q^2+1)j}
    spread = [frozenset((i + (q*q + 1) * j) % n for j in range(q + 1)) for i in range(q*q + 1)]
    assert all(L in lines and b(d, *lines[L]) == 0 for L in spread)
    assert len(set().union(*spread)) == n
    # remark: general delta0 with bar(delta0) = -delta0: delta0 = d*k, k in K*
    Kstar = [E.exp[(q*q + 1) * j] for j in range(q*q - 1)]
    Fstar = set(E.exp[n * j] for j in range(q - 1))
    mism = 0; tested = 0
    for k in Kstar[:q + 1]:
        delta0 = E.mul(d, k)
        ti0 = [L for L, (y, z) in lines.items() if b(delta0, y, z) == 0]
        for a in range(q + 1):
            for c in range(a, q + 1):
                if a == c: continue
                is2 = all(sum(1 for i in L if cls(i) in (a, c)) == 2 for L in ti0)
                pred = E.mul(E.pw(h, a + c), E.mul(delta0, delta0)) in Fstar
                tested += 1; mism += (is2 != pred)
    print(f"   remark after Prop 4.10 (delta0 general): {tested} (delta0,a,b) cases, mismatches between '2-ovoid' and 'h^(a+b) delta0^2 in F*': {mism}")
    # Corollary 4.11 graph
    tlist = sorted(ti, key=sorted); lid = {L: k for k, L in enumerate(tlist)}
    a = 0; O = [i for i in range(n) if cls(i) in (a, q - a)]
    nP = n; nL = len(tlist)
    edges = [(i, nP + k) for k, L in enumerate(tlist) for i in L]
    on = {i: [k for k, L in enumerate(tlist) if i in L] for i in range(n)}
    base = nP + nL
    clone = {P: base + j for j, P in enumerate(O)}
    for P in O:
        for k in on[P]: edges.append((clone[P], nP + k))
    sh = []
    base2 = base + len(O)
    for L in spread:
        for copy in range(2):
            v = base2 + len(sh); sh.append(v)
            for i in L: edges.append((i, v))
    N = base2 + len(sh)
    with open(f"singer_cor411_q{q}.edges", "w") as f:
        f.write(f"{N} {len(edges)}\n" + "\n".join(f"{u} {v}" for u, v in edges) + "\n")
    # regular completion: clone c_i to shadow y_{2i}, y_{2i+1}
    B = len(sh); cl = list(clone.values())
    edges2 = edges + [(cl[i], sh[(2 * i + e) % B]) for i in range(len(cl)) for e in (0, 1)]
    with open(f"singer_cor411_q{q}_reg.edges", "w") as f:
        f.write(f"{N} {len(edges2)}\n" + "\n".join(f"{u} {v}" for u, v in edges2) + "\n")
    print(f"   Cor 4.11 graph: {N} vertices (2(q^2+1)(q+3)={2*(q*q+1)*(q+3)})")
for q in map(int, sys.argv[1:] or [3, 5]):
    run(q)
