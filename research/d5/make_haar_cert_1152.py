"""Certificates for the (7,5) Haar record on 1152 vertices: the Haar graph of S_4 x Z_24.

  python3 research/d5/make_haar_cert_1152.py          (from the repository root)

Group G = Equiv.Perm (Fin 4) x Multiplicative (ZMod 24), order 576. A permutation is a tuple f with
f[i] = f(i), and (f, c) * (h, d) = (f o h, c + d), so (f o h)[i] = f[h[i]]. The connection set S is
the seven elements of the brief, in its order.

For every g in G the script finds indices (i, j, k, l) into S with

  cert1: g = s_i^-1 * s_j * s_k^-1 * s_l        (covers (S^-1 S)^2)
  cert2: g = s_i * s_j^-1 * s_k * s_l^-1        (covers (S S^-1)^2)

It then checks every certificate by explicit multiplication, checks the covering statements, and checks
the Haar graph on G x {A, B} by breadth-first search (degree 7, bipartite, diameter 5). Writes the
certificates to research/d5/haar_cert_1152.json. The Lean side (Cert1152.lean, Record1152.lean) is
not written yet: the Lean build could not be run in this environment.
"""
import itertools
import json
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research" / "d5" / "haar_cert_1152.json"

M = 24
PERMS = 4

# Connection set S: (permutation in one-line form [f 0, f 1, f 2, f 3], element of Z_24).
S = [
    ((0, 1, 2, 3), 0),
    ((1, 0, 3, 2), 23),
    ((3, 1, 0, 2), 0),
    ((2, 1, 0, 3), 18),
    ((1, 2, 3, 0), 18),
    ((0, 2, 3, 1), 17),
    ((0, 2, 1, 3), 3),
]


def mul(g, h):
    (f, c), (k, d) = g, h
    return (tuple(f[k[i]] for i in range(PERMS)), (c + d) % M)


def inv(g):
    f, c = g
    finv = [0] * PERMS
    for i in range(PERMS):
        finv[f[i]] = i
    return (tuple(finv), (-c) % M)


ONE = ((0, 1, 2, 3), 0)
ALL = [(p, c) for p in itertools.permutations(range(PERMS)) for c in range(M)]
assert len(ALL) == 576 and len(set(ALL)) == 576
assert len(set(S)) == 7


def form1(s, t):
    """s^-1 t, the factor of cert1."""
    return mul(inv(s), t)


def form2(s, t):
    """s t^-1, the factor of cert2."""
    return mul(s, inv(t))


def certificate(g, op):
    """Indices (i, j, k, l) with g = op(s_i, s_j) * op(s_k, s_l)."""
    pairs = {}
    for i in range(len(S)):
        for j in range(len(S)):
            pairs.setdefault(op(S[i], S[j]), (i, j))
    for k in range(len(S)):
        for l in range(len(S)):
            x = mul(g, inv(op(S[k], S[l])))
            if x in pairs:
                i, j = pairs[x]
                return (i, j, k, l)
    raise AssertionError(("no certificate", g))


def check_cert1(g, w):
    i, j, k, l = w
    return mul(mul(mul(inv(S[i]), S[j]), inv(S[k])), S[l]) == g


def check_cert2(g, w):
    i, j, k, l = w
    return mul(mul(mul(S[i], inv(S[j])), S[k]), inv(S[l])) == g


def haar_check():
    """BFS on the Haar graph: vertices (g, 0) = A-side and (g, 1) = B-side; (g, A) ~ (s g, B)."""
    index = {g: n for n, g in enumerate(ALL)}
    adj = [set() for _ in range(2 * len(ALL))]
    for g in ALL:
        for s in S:
            h = mul(s, g)
            u = index[g]
            v = len(ALL) + index[h]
            adj[u].add(v)
            adj[v].add(u)
    n = 2 * len(ALL)
    assert all(len(a) == len(S) for a in adj), "not 7-regular"
    color = [-1] * n
    color[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for y in adj[x]:
            if color[y] < 0:
                color[y] = 1 - color[x]
                queue.append(y)
            else:
                assert color[y] != color[x], "not bipartite"
    diameter = 0
    for src in range(n):
        dist = [-1] * n
        dist[src] = 0
        queue = deque([src])
        while queue:
            x = queue.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    queue.append(y)
        assert min(dist) >= 0, "disconnected"
        diameter = max(diameter, max(dist))
    return n, diameter


def main():
    cert1, cert2 = {}, {}
    for g in ALL:
        cert1[g] = certificate(g, form1)
        cert2[g] = certificate(g, form2)
        assert check_cert1(g, cert1[g]), ("cert1 fails", g)
        assert check_cert2(g, cert2[g]), ("cert2 fails", g)
    # covering statements, as the Lean hypotheses hA, hB are stated: g = a^-1 b c^-1 d and g = a b^-1 c d^-1
    for g in ALL:
        i, j, k, l = cert1[g]
        assert g == mul(mul(mul(inv(S[i]), S[j]), inv(S[k])), S[l])
        i, j, k, l = cert2[g]
        assert g == mul(mul(mul(S[i], inv(S[j])), S[k]), inv(S[l]))
    n, diameter = haar_check()
    assert n == 1152 and diameter == 5, (n, diameter)
    data = {
        "group": "Equiv.Perm (Fin 4) x Multiplicative (ZMod 24)",
        "order": 576,
        "S": [{"perm": list(p), "z": c} for p, c in S],
        "cert1": [list(cert1[g]) for g in ALL],
        "cert2": [list(cert2[g]) for g in ALL],
        "elements": [{"perm": list(p), "z": c} for p, c in ALL],
    }
    OUT.write_text(json.dumps(data, indent=1) + "\n")
    print("ok: 576 elements, both certificates checked, Haar graph on", n,
          "vertices, 7-regular, bipartite, diameter", diameter, "; wrote", OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
