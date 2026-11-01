#!/usr/bin/env python3
"""mklift.py SOL EDGES: edge list ("n" then "u v" lines) of the lift described by a lift4 solution file
(header "m k r p cost", then 4p lines "eu ev ea"). Vertex u*N+g, u < 2p; whites u < p. Usage: mklift.py SOL EDGES"""
import sys
def load(fn):
    with open(fn) as f:
        m, k, r, p, c = map(int, f.readline().split())
        E = [tuple(map(int, l.split())) for l in f if l.strip()]
    return m, k, r, p, E
def edges(m, k, r, p, E):
    N = m * k
    R = [pow(r, j, m) for j in range(k)]
    def gmul(g, h):
        a, j = divmod(g, k); b, i = divmod(h, k)
        return ((a + R[j] * b) % m) * k + (j + i) % k
    def ginv(g):
        a, j = divmod(g, k); jj = (k - j) % k
        return ((-a) % m * R[jj] % m) * k + jj
    out = []
    for eu, ev, ea in E:
        for g in range(N):
            out.append((eu * N + g, ev * N + gmul(g, ea)))
    return 2 * p * N, out
if __name__ == "__main__":
    m, k, r, p, E = load(sys.argv[1])
    n, ed = edges(m, k, r, p, E)
    with open(sys.argv[2], "w") as f:
        f.write(f"{n}\n")
        f.write("".join(f"{u} {v}\n" for u, v in ed))
    print("n", n, "edges", len(ed))
