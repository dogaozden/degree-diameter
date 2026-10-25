"""PGRP writer for Frobenius-type affine groups G = F_Q x| C_m (x -> w^k x + a), w of order m in F_Q^*.
Element (a,k) has index k*Q + enc(a); identity = 0. Left multiplication (a,k)(b,l) = (a + w^k b, k + l).
Generators: translations by 1 (and by s if F_Q = F_p[s]/(s^2 - nonsq)), and the rotation (0,1).
Order-20 subgroups: rotation groups about points p: H_p = {((1 - w^{t j}) p, t j)}, t = m/20, j = 0..19;
involution c = (2p, m/2). Usage: mkaff.py P [P2] m NSUB seed OUT.pgrp
  - P prime: F_Q = Z_P (no P2)
  - P=19, P2 given as "sq:2" meaning F_361 = F_19[s]/(s^2-2)"""
import sys, random

def build_field(kind):
    if kind[0] == 'prime':
        p = kind[1]
        Q = p
        add = lambda x, y: (x + y) % p
        mul = lambda x, y: (x * y) % p
        neg = lambda x: (-x) % p
        enc = lambda x: x
        elems = list(range(p))
        gens_add = [1]
    else:
        p, nr = kind[1], kind[2]          # F_{p^2} = F_p[s]/(s^2 - nr)
        Q = p * p
        def add(x, y):
            return ((x % p + y % p) % p) + p * ((x // p + y // p) % p)
        def mul(x, y):
            a0, a1, b0, b1 = x % p, x // p, y % p, y // p
            return ((a0 * b0 + nr * a1 * b1) % p) + p * ((a0 * b1 + a1 * b0) % p)
        def neg(x):
            return ((-(x % p)) % p) + p * ((-(x // p)) % p)
        enc = lambda x: x
        elems = list(range(Q))
        gens_add = [1, p]                  # 1 and s
    return Q, add, mul, neg, elems, gens_add

def power(mul, x, e, one):
    r = one
    while e:
        if e & 1: r = mul(r, x)
        x = mul(x, x); e >>= 1
    return r

def main():
    args = sys.argv[1:]
    if args[0] == 'prime':
        kind = ('prime', int(args[1])); rest = args[2:]
    else:
        kind = ('sq', int(args[1]), int(args[2])); rest = args[3:]
    m, nsub, seed, out = int(rest[0]), int(rest[1]), int(rest[2]), rest[3]
    Q, add, mul, neg, elems, gens_add = build_field(kind)
    one = 1
    # primitive element of F_Q^* (order Q-1)
    order_units = Q - 1
    def order_of(x):
        k, y = 1, x
        while y != one:
            y = mul(y, x); k += 1
        return k
    g = next(x for x in elems if x not in (0, 1) and order_of(x) == order_units)
    w = power(mul, g, order_units // m, one)
    assert power(mul, w, m, one) == one and power(mul, w, m // 2, one) == neg(one) and m % 20 == 0
    wp = [power(mul, w, k, one) for k in range(m)]
    N = m * Q
    def idx(a, k): return (k % m) * Q + a
    def el(i): return i % Q, i // Q
    def lmul(gA, gk, y):
        # left multiplication by (gA, gk) on element y=(b,l)
        b, l = el(y)
        return idx(add(gA, mul(wp[gk], b)), gk + l)
    gens = [(a, 0) for a in gens_add] + [(0, 1)]
    perms = []
    for (ga, gk) in gens:
        perms.append([lmul(ga, gk, y) for y in range(N)])
    # subgroups: rotation groups about points p; use a random subset of nsub points (keep 0)
    rng = random.Random(seed)
    pts = list(range(Q))
    rng.shuffle(pts)
    pts = [0] + [p for p in pts if p != 0][:nsub - 1]
    t = m // 20
    subs = []
    for p in pts:
        H = []
        for j in range(20):
            k = (t * j) % m
            a = mul(add(one, neg(wp[k])), p)
            H.append(idx(a, k))
        c = idx(add(p, p), m // 2)
        assert c in H and lmul(0, 0, c) == c
        subs.append((c, H))
    with open(out, 'w') as f:
        f.write(f"{N} {len(perms)} 0 20 {len(subs)}\n")
        for pm in perms: f.write(" ".join(map(str, pm)) + "\n")
        for c, H in subs: f.write(f"{c} " + " ".join(map(str, H)) + "\n")
    print(f"N={N} Q={Q} m={m} gens={len(perms)} subgroups={len(subs)} w={w} -> {out}")

main()
