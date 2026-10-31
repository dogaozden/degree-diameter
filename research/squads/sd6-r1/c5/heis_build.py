#!/usr/bin/env python3
r"""Independent builder + checker for Haar graphs on G = Heis(q) x Z_n (c5 card).

Group: elements (a,b,c,z), a,b,c in GF(q) (q prime here), z in Z_n;
product (a,b,c,z)(a',b',c',z') = (a+a', b+b', c+c'+a*b', z+z' mod n)  (same law as haar_sd's `heis q`).
Haar graph H(G,S): vertices (g,A) -> idx(g), (g,B) -> N + idx(g); edges (g,A) ~ (s g, B), s in S.
Writes an edge list for research/selfdual-d6/src/apsp ("2N" line, then "a b" lines).

Usage:
  heis_build.py SOL.sol OUT.edges      (SOL.sol: haar_sd solution file with `heis q` group)
Prints: N, the uncovered count |G \ S S^-1 S S^-1 S| (exact, independent of apsp), and writes OUT.edges.
Run `apsp OUT.edges d 6` afterwards for the BFS verdict.
"""
import re
import sys


def parse_sol(path):
    lines = open(path).read().strip().splitlines()
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    m = re.search(r'heis\s+(\d+)', lines[0])
    q = int(m.group(1))
    n = int(re.search(r'\bn\s+(\d+)', lines[0]).group(1))
    S = []
    for ln in lines[1:]:
        mm = re.search(r'heis\((\d+),(\d+),(\d+)\)\s+z=(\d+)', ln)
        if mm:
            S.append(tuple(int(x) for x in mm.groups()))
    return d, D, q, n, S


def mul(g, h, q, n):
    a, b, c, z = g
    a2, b2, c2, z2 = h
    return ((a + a2) % q, (b + b2) % q, (c + c2 + a * b2) % q, (z + z2) % n)


def idx(g, q, n):
    a, b, c, z = g
    return ((a * q + b) * q + c) * n + z


def inv(g, q, n):
    # brute-free inverse: solve g * x = e  ->  x = (-a, -b, -c + a*b, -z)
    a, b, c, z = g
    return ((-a) % q, (-b) % q, (-c + a * b) % q, (-z) % n)


def main():
    sol, out = sys.argv[1], sys.argv[2]
    d, D, q, n, S = parse_sol(sol)
    N = q * q * q * n
    assert len(S) == d, (len(S), d)
    assert len(set(S)) == d, "repeated generator"
    assert (0, 0, 0, 0) in S, "identity not in S"
    # uncovered count for even D: |G \ S S^-1 S S^-1 S|
    Sinv = [inv(s, q, n) for s in S]
    words = set()
    for s1 in S:
        for i2 in Sinv:
            p12 = mul(s1, i2, q, n)
            for s3 in S:
                p123 = mul(p12, s3, q, n)
                for i4 in Sinv:
                    p1234 = mul(p123, i4, q, n)
                    for s5 in S:
                        words.add(mul(p1234, s5, q, n))
    uncovered = N - len(words)
    # edge list
    with open(out, 'w') as f:
        f.write('%d\n' % (2 * N))
        for a in range(q):
            for b in range(q):
                for c in range(q):
                    for z in range(n):
                        g = (a, b, c, z)
                        gi = idx(g, q, n)
                        for s in S:
                            sg = mul(s, g, q, n)
                            f.write('%d %d\n' % (gi, N + idx(sg, q, n)))
    print('N=%d d=%d D=%d q=%d n=%d uncovered=%d coverage=%.4f words=%d' %
          (N, d, D, q, n, uncovered, len(words) / N, len(words)))


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    main()
