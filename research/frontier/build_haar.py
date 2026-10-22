"""Rebuild a Haar graph from a haar_gen solution file, independently of the C search code.

Usage: python3 build_haar.py SOLUTION.txt OUT.edges.txt
Solution header: "d D <group spec> n NCYC N NTOT", group spec = meta m k r | sl p | psl p | pgl p | cyc;
then d lines "<index> <description>", description mat(a,b,c,d) z=Z, meta(a=A,j=J) z=Z, or z=Z.
Only the descriptions are used (indices are ignored). Graph: vertices (g,A) -> id(g), (g,B) -> N + id(g),
edges (g,A) ~ (s g, B) for s in S. Writes a plain edge list: first line n, then "u v" per line.
Also checks the diameter from (e,A) and (e,B) by BFS (enough for a Haar graph, since right multiplication
is an automorphism group transitive on each side), and prints the result.
"""
import re
import sys
from collections import deque
from itertools import product


def group(spec, ncyc):
    kind = spec[0]
    if kind == "meta":
        m, k, r = map(int, spec[1:])
        assert pow(r, k, m) == 1 % m
        els = [(a, j) for a in range(m) for j in range(k)]
        mul = lambda x, y: ((x[0] + pow(r, x[1], m) * y[0]) % m, (x[1] + y[1]) % k)
        e = (0, 0)
    elif kind == "cyc":
        els, mul, e = [()], (lambda x, y: ()), ()
    else:
        p = int(spec[1])

        def canon(M):
            a, b, c, d = (v % p for v in M)
            if kind == "sl":
                return (a, b, c, d)
            first = next(v for v in (a, b, c, d) if v)
            if kind == "psl":
                if first > p // 2:
                    a, b, c, d = (-a) % p, (-b) % p, (-c) % p, (-d) % p
                return (a, b, c, d)
            inv = pow(first, p - 2, p)
            return (a * inv % p, b * inv % p, c * inv % p, d * inv % p)

        def mul(X, Y):
            a, b, c, d = X
            A, B, C, D = Y
            return canon((a * A + b * C, a * B + b * D, c * A + d * C, c * B + d * D))

        want_det1 = kind in ("sl", "psl")
        els = sorted({canon(M) for M in product(range(p), repeat=4)
                      if (M[0] * M[3] - M[1] * M[2]) % p and (not want_det1 or (M[0] * M[3] - M[1] * M[2]) % p == 1)})
        e = canon((1, 0, 0, 1))
        G0mul = mul
        globals()["_canon"] = canon
    G = [(x, z) for x in els for z in range(ncyc)]
    gm = lambda X, Y: (mul(X[0], Y[0]), (X[1] + Y[1]) % ncyc)
    return G, gm, (e, 0)


def main():
    sol, out = sys.argv[1], sys.argv[2]
    lines = open(sol).read().split("\n")
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    i = head.index("n")
    spec, ncyc = head[2:i], int(head[i + 1])
    G, gm, e = group(spec, ncyc)
    N = len(G)
    idx = {g: t for t, g in enumerate(G)}
    S = []
    for ln in lines[1:1 + d]:
        z = int(re.search(r"z=(\d+)", ln).group(1))
        if "mat(" in ln:
            M = tuple(int(v) for v in re.search(r"mat\(([^)]*)\)", ln).group(1).split(","))
            x = _canon(M)
        elif "meta(" in ln:
            a, j = map(int, re.search(r"meta\(a=(\d+),j=(\d+)\)", ln).groups())
            x = (a, j)
        else:
            x = ()
        S.append((x, z))
    assert len(set(S)) == d and all(s in idx for s in S)
    edges = []
    for g in G:
        for s in S:
            edges.append((idx[g], N + idx[gm(s, g)]))
    n = 2 * N
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    for src in (idx[e], N + idx[e]):
        dist = [-1] * n
        dist[src] = 0
        q = deque([src])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    q.append(y)
        print("ecc from", "A" if src < N else "B", "=", max(dist), "unreached", dist.count(-1))
    print("n =", n, "edges =", len(edges), "max degree =", max(len(a) for a in adj))
    with open(out, "w") as f:
        f.write(f"{n}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")


if __name__ == "__main__":
    main()
