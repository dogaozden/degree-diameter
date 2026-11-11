#!/usr/bin/env python3
"""Print group specs (for lift_ex) of a given order N: metacyclic, Z_p^2 x|_M Z_k, and products with a cyclic factor.
Usage: gen_specs.py N [--prod] [--nometa]  -> one spec per line, '#' comments excluded."""
import sys, itertools

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def metas(n):
    out = []
    for k in divisors(n):
        m = n // k
        for r in range(m):
            if pow(r, k, m) == 1 % m:
                out.append(f"meta {m} {k} {r}")
    return out

def gl2_elems(p):
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a * d - b * c) % p:
            yield (a, b, c, d)

def mat_pow(M, j, p):
    R = (1 % p, 0, 0, 1 % p)
    for _ in range(j):
        a, b, c, d = R
        R = ((a * M[0] + b * M[2]) % p, (a * M[1] + b * M[3]) % p, (c * M[0] + d * M[2]) % p, (c * M[1] + d * M[3]) % p)
    return R

def zp2s(n):
    out = []
    for p in [2, 3, 5, 7, 11, 13]:
        if n % (p * p):
            continue
        k = n // (p * p)
        for M in gl2_elems(p):
            if mat_pow(M, k, p) == (1 % p, 0, 0, 1 % p):
                out.append(f"zp2 {p} {k} {M[0]} {M[1]} {M[2]} {M[3]}")
    return out

if __name__ == "__main__":
    n = int(sys.argv[1]); flags = sys.argv[2:]
    specs = []
    if "--nometa" not in flags:
        specs += metas(n)
    specs += zp2s(n)
    if "--prod" in flags:
        for c in divisors(n):
            if 1 < c < n:
                d = n // c
                specs += [f"prod {s} cyc {c}" for s in metas(d) + zp2s(d)]
    seen = set()
    for s in specs:
        if s not in seen:
            seen.add(s); print(s)
