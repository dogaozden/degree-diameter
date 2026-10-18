"""Build the Haar graph from a haar_search solution file and save it as record JSON.

Usage: python3 build_haar.py SOLUTION.txt OUT.json
Solution file: first line "d m k lam", then d lines "a j" (elements of Z_m x|_lam Z_k).
Vertex (g, A) has index g, (g, B) has index N + g, g = a*k + j. Edge (g,A) ~ (s g, B).
"""
import json
import sys


def main(sol, out):
    rows = [list(map(int, l.split())) for l in open(sol) if l.strip()]
    d, m, k, lam = rows[0]
    S = [tuple(r) for r in rows[1:]]
    assert len(S) == d
    N = m * k
    pw = [pow(lam, j, m) for j in range(k)]

    def mul(g, h):
        (a, j), (b, l) = g, h
        return ((a + pw[j] * b) % m, (j + l) % k)

    edges = []
    for a in range(m):
        for j in range(k):
            g = (a, j)
            for s in S:
                h = mul(s, g)
                edges.append([a * k + j, N + h[0] * k + h[1]])
    json.dump({"case": f"d{d}D5", "value": 2 * N, "output": [2 * N, edges],
               "construction": {"group": f"Z_{m} x|_{lam} Z_{k}", "S": S}}, open(out, "w"))
    print(out, 2 * N, len(edges))


if __name__ == "__main__":
    main(*sys.argv[1:3])
