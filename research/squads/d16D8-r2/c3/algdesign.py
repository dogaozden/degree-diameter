#!/usr/bin/env python3
# c3: algebraic voltages for Z_m lifts of I(W(q)) + 2 matchings.
# usage: python3 algdesign.py FLAGS q m seed OUT [MATCH_ROT]
#   FLAGS = rand | singer | fq | dlogq1 | dlogq2
#     singer  : flag (p,L) gets the Singer index in Z_(q+1) of the PG(1,q)-parameter of p on L
#               (basis u,v = first two points of L, p = a u + b v, z = a + b w in F_(q^2), index of z^(q-1))
#     fq      : flag gets t = b/a in F_q (additive group Z_q), inf -> 0
#     dlogq1  : flag gets dlog_{F_q^*}(t) in Z_(q-1), t = b/a (0, inf -> 0)
#     dlogq2  : flag gets dlog_{F_(q^2)^*}(1 + t w) in Z_(q^2-1) (inf -> dlog(w)); needs m | q^2-1 (q <= 7)
#   the flag voltage is multiplied by t = m / order (embedding) when the order divides m: m = t * order.
#   matchings: two random perfect matchings points -> lines with random voltages (cls 100, 101).
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/d16D8')
import gq

def factor(n):
    f = []; d = 2
    while d * d <= n:
        while n % d == 0:
            f.append(d); n //= d
        d += 1
    if n > 1: f.append(n)
    return f

def nonres(q):
    sq = {(x * x) % q for x in range(1, q)}
    return next(x for x in range(2, q) if x not in sq)

def gen_cyclic(order, mul, one, elems):
    """find a generator of the cyclic group of given order (elems = all nonzero elements)"""
    for g in elems:
        cur = one; seen = {}
        ok = True
        for k in range(order):
            if cur in seen: ok = False; break
            seen[cur] = k
            cur = mul(cur, g)
        if ok and cur == one and len(seen) == order:
            return g, seen
    raise RuntimeError('no generator')

def build_tables(q):
    n = nonres(q)
    def mul2(x, y): return ((x[0] * y[0] + n * x[1] * y[1]) % q, (x[0] * y[1] + x[1] * y[0]) % q)
    elems2 = [(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)]
    h, dl2 = gen_cyclic(q * q - 1, mul2, (1, 0), elems2)     # dl2[z] = k with h^k = z
    mul1 = lambda x, y: x * y % q
    g1, dl1 = gen_cyclic(q - 1, mul1, 1, list(range(1, q)))  # dl1[t] = k with g1^k = t
    return dl2, dl1

def design(flags, q, m, seed, out, match_rot=None):
    G = gq.load(q); N = G['N']; pts = G['pts']; lines = G['lines']
    rnd = random.Random(seed)
    dl2, dl1 = build_tables(q)
    edges = []
    for l, L in enumerate(lines):
        u = pts[L[0]]; v = pts[L[1]]
        # coordinate pair (i,j) with nonzero 2x2 determinant for the basis (u,v)
        ij = None
        for i in range(4):
            for j in range(4):
                if (u[i] * v[j] - u[j] * v[i]) % q:
                    ij = (i, j); break
            if ij: break
        i, j = ij; D = (u[i] * v[j] - u[j] * v[i]) % q; Dinv = pow(D, q - 2, q)
        for p in L:
            w = pts[p]
            a = (w[i] * v[j] - v[i] * w[j]) * Dinv % q     # w = a u + b v
            b = (u[i] * w[j] - w[i] * u[j]) * Dinv % q
            # z = a + b w (w = omega in F_(q^2)); representative with a != 0 normalised to 1 when possible
            if flags == 'rand':
                c = rnd.randrange(m)
            elif flags == 'singer':
                c = dl2[(a, b)] % (q + 1)                    # index in Z_(q+1)
                c = c * (m // (q + 1)) if m % (q + 1) == 0 else c % m
            elif flags == 'fq':
                t = b * pow(a, q - 2, q) % q if a else 0     # t in F_q
                c = t * (m // q) if m % q == 0 else t % m
            elif flags == 'dlogq1':
                t = b * pow(a, q - 2, q) % q if a else 0
                k = dl1[t] if t else 0                       # Z_(q-1)
                c = k * (m // (q - 1)) if m % (q - 1) == 0 else k % m
            elif flags == 'dlogq2':
                if a:
                    zi = dl2[(1, b * pow(a, q - 2, q) % q)]   # normalised rep 1 + t w
                else:
                    zi = dl2[(0, 1)]
                c = zi % m if (q * q - 1) % m == 0 else zi * 0
                if (q * q - 1) % m: raise SystemExit('m must divide q^2-1')
            else:
                raise SystemExit('unknown flags ' + flags)
            edges.append((p, N + l, c, 1))
    for k in range(2):
        perm = list(range(N)); rnd.shuffle(perm)
        for p in range(N):
            edges.append((p, N + perm[p], rnd.randrange(m), 100 + k))
    gq.write_base(out, 2 * N, m, edges)
    return out

if __name__ == '__main__':
    flags, q, m, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    design(flags, q, m, seed, out)
    print(out)
