#!/usr/bin/env python3
"""Write the multiplication table of a Mobius group H = PSL(2,q) or PGL(2,q) (q = p^k) as a binary file.

File format (little endian): uint32 h, then h*h uint16 entries MH[a*h+b] = index of a*b (product in H).
Index 0 is the identity. Usage: mkgroup.py psl|pgl q outfile
"""
import sys, struct

class GF:
    def __init__(self, p, k, f=None):
        self.p, self.k, self.q, self.f = p, k, p ** k, f
        q = self.q
        self.mul = [[self.idx(self.pmul(self.vec(a), self.vec(b))) for b in range(q)] for a in range(q)]
        self.add = [[self.idx([(x + y) % p for x, y in zip(self.vec(a), self.vec(b))]) for b in range(q)] for a in range(q)]
        self.neg = [self.idx([(-x) % p for x in self.vec(a)]) for a in range(q)]
        self.inv = [0] * q
        for a in range(1, q):
            for b in range(1, q):
                if self.mul[a][b] == 1:
                    self.inv[a] = b

    def vec(self, a):
        return [(a // self.p ** i) % self.p for i in range(self.k)]

    def idx(self, v):
        return sum(c * self.p ** i for i, c in enumerate(v))

    def pmul(self, va, vb):
        p, k = self.p, self.k
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(va):
            for j, y in enumerate(vb):
                prod[i + j] = (prod[i + j] + x * y) % p
        for d in range(2 * k - 2, k - 1, -1):      # reduce by monic f of degree k
            c = prod[d]
            if c:
                prod[d] = 0
                for i in range(k):
                    prod[d - k + i] = (prod[d - k + i] - c * self.f[i]) % p
        return prod[:k]

def field(q):
    table = {2: (2, 1, None), 3: (3, 1, None), 5: (5, 1, None), 7: (7, 1, None), 11: (11, 1, None),
             13: (13, 1, None), 8: (2, 3, [1, 1, 0]), 9: (3, 2, [1, 0]), 16: (2, 4, [1, 1, 0, 0])}
    p, k, f = table[q]
    return GF(p, k, f)

def mobius_group(q, kind):
    F = field(q)
    INF = q
    def order(a):
        x, o = a, 1
        while x != 1:
            x = F.mul[x][a]; o += 1
        return o
    g = next(a for a in range(1, q) if order(a) == q - 1)
    mult = g if (kind == 'pgl' or q % 2 == 0) else F.mul[g][g]
    def tup(fn):
        return tuple(fn(x) for x in range(q + 1))
    T = tup(lambda x: INF if x == INF else F.add[x][1])
    def sinv(x):
        if x == INF: return 0
        if x == 0: return INF
        return F.neg[F.inv[x]]
    S = tup(sinv)
    M = tup(lambda x: INF if x == INF else F.mul[mult][x])
    ident = tuple(range(q + 1))
    def comp(a, b):   # (a*b)(x) = a(b(x))
        return tuple(a[b[x]] for x in range(q + 1))
    elems = [ident]; index = {ident: 0}
    stack = [ident]
    while stack:
        x = stack.pop()
        for gen in (T, S, M):
            y = comp(gen, x)
            if y not in index:
                index[y] = len(elems); elems.append(y); stack.append(y)
    return elems, index, comp

def main():
    kind, q, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    elems, index, comp = mobius_group(q, kind)
    h = len(elems)
    exp = q * (q * q - 1) // (2 if kind == 'psl' and q % 2 == 1 else 1)
    assert h == exp, (h, exp)
    MH = [0] * (h * h)
    for a in range(h):
        ea = elems[a]
        for b in range(h):
            MH[a * h + b] = index[comp(ea, elems[b])]
    # associativity spot check
    import random
    rnd = random.Random(1)
    for _ in range(2000):
        a, b, c = (rnd.randrange(h) for _ in range(3))
        assert MH[MH[a * h + b] * h + c] == MH[a * h + MH[b * h + c]]
    with open(out, 'wb') as fh:
        fh.write(struct.pack('<I', h))
        fh.write(struct.pack('<%dH' % (h * h), *MH))
    print(f"{kind} q={q} order={h} written {out}")

if __name__ == '__main__':
    main()
