#!/usr/bin/env python3
"""c16 independent checker for haar_gen3 solution files over sl/psl/pgl p x Z_n with n = 1 (prime fields only).
Haar graph H(G,S): vertices (g,A),(g,B); edges (g,A)~(s g,B). Right multiplication is transitive on each side, so
diameter = max(ecc(e,A), ecc(e,B)); both BFS must reach all 2|G| vertices. Usage: check_haar.py SOL"""
import sys
from collections import deque

def main(path):
    lines = open(path).read().split("\n")
    hdr = lines[0].split()
    d, D = int(hdr[0]), int(hdr[1])
    fam, p = hdr[2], int(hdr[3])
    assert hdr[4] == "n" and int(hdr[5]) == 1, "only n = 1 supported here"
    gens = []
    for ln in lines[1:]:
        if not ln.strip():
            continue
        # "<index> mat(a,b,c,d) z=Z"
        inside = ln[ln.index("mat(") + 4: ln.index(")")]
        a, b, c, dd = (int(x) for x in inside.split(","))
        gens.append((a, b, c, dd))
    assert len(gens) == d, (len(gens), d)

    def canon(m):
        a, b, c, dd = [x % p for x in m]
        if fam == "pgl":
            for x in (a, b, c, dd):
                if x:
                    inv = pow(x, p - 2, p)
                    return tuple(y * inv % p for y in (a, b, c, dd))
            raise ValueError("zero matrix")
        if fam == "psl":
            t = (a, b, c, dd)
            n = tuple((-y) % p for y in t)
            return min(t, n)
        return (a, b, c, dd)  # sl

    def mul(x, y):
        a, b, c, dd = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + dd * g) % p, (c * f + dd * h) % p)

    def det(x):
        return (x[0] * x[3] - x[1] * x[2]) % p

    # enumerate the group
    G = []
    seen = set()
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for dd in range(p):
                    m = (a, b, c, dd)
                    if det(m) == 0:
                        continue
                    if fam == "sl" and det(m) != 1:
                        continue
                    if fam == "psl" and det(m) != 1:
                        continue
                    cm = canon(m)
                    if cm not in seen:
                        seen.add(cm)
                        G.append(cm)
    N = len(G)
    idx = {g: i for i, g in enumerate(G)}
    e = canon((1, 0, 0, 1))
    ei = idx[e]
    # generators (canonical) and their inverses (adjugate is proportional to the inverse)
    S = [canon(s) for s in gens]
    Sinv = [canon((s[3], (-s[1]) % p, (-s[2]) % p, s[0])) for s in S]
    Lt = [[idx[canon(mul(s, g))] for g in G] for s in S]
    Lit = [[idx[canon(mul(s, g))] for g in G] for s in Sinv]

    def ecc(start_side):
        # vertices: side 0 = A, side 1 = B; id = side*N + i
        dist = [-1] * (2 * N)
        s0 = start_side * N + ei
        dist[s0] = 0
        q = deque([s0])
        reached = 1
        far = 0
        while q:
            v = q.popleft()
            side, i = divmod(v, N)
            dv = dist[v]
            if side == 0:
                nb = [(1, Lt[k][i]) for k in range(d)]
            else:
                nb = [(0, Lit[k][i]) for k in range(d)]
            for ns, ni in nb:
                w = ns * N + ni
                if dist[w] < 0:
                    dist[w] = dv + 1
                    reached += 1
                    if dv + 1 > far:
                        far = dv + 1
                    q.append(w)
        return far, reached

    eA, rA = ecc(0)
    eB, rB = ecc(1)
    ok = rA == 2 * N and rB == 2 * N
    print(f"group {fam} {p} x Z_1 N={N} (vertices {2*N}) d={d}: ecc(A)={eA} ecc(B)={eB} reached={rA},{rB}")
    print(f"diameter={max(eA, eB)} target D={D}: {'VALID' if ok and max(eA, eB) <= D else 'INVALID'}")

if __name__ == "__main__":
    main(sys.argv[1])
