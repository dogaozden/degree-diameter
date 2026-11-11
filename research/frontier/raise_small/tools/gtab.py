#!/usr/bin/env python3
"""gtab.py: multiplication tables in the own-small "GAP export" format read by salift_s, salift4, polish, score48.

  python3 gtab.py OUT  m k r [c]      one group  G = (Z_m x|_r Z_k) x Z_c   (c = 1 if omitted)
  python3 gtab.py OUT  --list FILE    one group per line of FILE: "m k r [c]"  (ids 1, 2, ... in file order)

Element (a, j, z), a in Z_m, j in Z_k, z in Z_c; index ((a*k + j)*c + z); identity = index 0.
Product (a,j,z)(b,l,w) = (a + r^j b mod m, j + l mod k, z + w mod c). Needs r^k = 1 mod m, gcd(r, m) = 1.
File format (salift_s): for each group a header "G N id name" then N*N integers (row g, column h = index of g*h).
"""
import sys
from math import gcd


def table(m, k, r, c=1):
    assert gcd(r, m) == 1 and pow(r, k, m) == 1 % m, (m, k, r)
    N = m * k * c
    rp = [pow(r, j, m) for j in range(k)]
    els = [(a, j, z) for a in range(m) for j in range(k) for z in range(c)]
    idx = lambda a, j, z: (a * k + j) * c + z
    rows = []
    for (a, j, z) in els:
        rj = rp[j]
        rows.append(' '.join(str(idx((a + rj * b) % m, (j + l) % k, (z + w) % c)) for (b, l, w) in els))
    return N, rows


def main():
    out = sys.argv[1]
    if sys.argv[2] == '--list':
        specs = [list(map(int, l.split())) for l in open(sys.argv[3]) if l.strip() and not l.startswith('#')]
    else:
        specs = [list(map(int, sys.argv[2:]))]
    with open(out, 'w') as f:
        for gid, sp in enumerate(specs, 1):
            m, k, r = sp[:3]; c = sp[3] if len(sp) > 3 else 1
            N, rows = table(m, k, r, c)
            f.write(f"G {N} {gid} meta_{m}_{k}_{r}_x{c}\n")
            f.write('\n'.join(rows)); f.write('\n')
            print(gid, N, f"meta {m} {k} {r} x{c}", file=sys.stderr)


if __name__ == '__main__':
    main()
