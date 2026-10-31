"""Independent helpers for the SL(2,17) Haar graph search (job d58-sl17).

Nothing here uses the C search code: the group is enumerated from 2x2 matrices mod 17 with determinant 1,
the Haar graph H(G,S) is built from S alone, and the edge list goes to lifts/coordinator_check/apsp.c.

Conventions (match the search): vertex g in A-side = index g, B-side = index N + g; edge (g,A) -- (s*g,B)
for s in S (left multiplication, matrix product s*g). Elements are printed as "a b c d" = [[a,b],[c,d]] row by row.
"""
import hashlib
import sys

P = 17


def mat_mul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def mat_inv(x):
    a, b, c, d = x  # det 1
    return (d % P, (-b) % P, (-c) % P, a % P)


def group():
    """All 2x2 matrices over GF(17) with determinant 1, in a fixed order; returns (elements, index dict)."""
    els = []
    for a in range(P):
        for b in range(P):
            for c in range(P):
                for d in range(P):
                    if (a * d - b * c) % P == 1:
                        els.append((a, b, c, d))
    idx = {m: i for i, m in enumerate(els)}
    assert len(els) == P * (P * P - 1), len(els)  # |SL(2,17)| = 4896
    return els, idx


def parse_S(text):
    """S from lines or one line of 4-tuples: 'a b c d' per element, d elements, first = identity."""
    nums = [int(t) for t in text.replace("|", " ").split()]
    assert len(nums) % 4 == 0
    S = [tuple(x % P for x in nums[i:i + 4]) for i in range(0, len(nums), 4)]
    return S


def edges_of(S, els, idx):
    N = len(els)
    E = []
    for s in S:
        for g in range(N):
            sg = mat_mul(s, els[g])
            E.append((g, N + idx[sg]))
    return N, E


def write_edge_list(S, path):
    els, idx = group()
    for s in S:
        assert s in idx, s
    N, E = edges_of(S, els, idx)
    with open(path, "w") as f:
        f.write(f"{2 * N}\n")
        for u, v in E:
            f.write(f"{u} {v}\n")
    return 2 * N, len(E)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def uncovered_bfs(S, els, idx, D=8):
    """Independent cost: B-side elements at distance > D-1 from (e,A) in H(G,S), by plain BFS."""
    from collections import deque
    N = len(els)
    e = idx[(1, 0, 0, 1)]
    Sset = S
    Lmul = {s: [idx[mat_mul(s, els[g])] for g in range(N)] for s in Sset}
    Linv = {s: [0] * N for s in Sset}
    for s in Sset:
        si = mat_inv(s)
        # A-neighbours of (h,B): (s^-1 h, A) for each s in S; s^-1 * h
        Linv[s] = [idx[mat_mul(si, els[h])] for h in range(N)]
    dist = {}
    start = (e, 0)  # side 0 = A, 1 = B
    dist[start] = 0
    dq = deque([start])
    while dq:
        v = dq.popleft()
        dv = dist[v]
        g, side = v
        if dv >= D:
            continue
        if side == 0:
            for s in Sset:
                w = (Lmul[s][g], 1)
                if w not in dist:
                    dist[w] = dv + 1
                    dq.append(w)
        else:
            for s in Sset:
                w = (Linv[s][g], 0)
                if w not in dist:
                    dist[w] = dv + 1
                    dq.append(w)
    total_B = sum(1 for g in range(N) if (g, 1) in dist and dist[(g, 1)] <= D - 1)
    return N - total_B


def canon_conj(S, els, idx):
    """Canonical form of S under conjugation by SL(2,17) (fixes e).
    Conjugation fixes e, so this is an invariant of the Haar graph family up to these symmetries (not a full
    isomorphism test). Returns the minimal sorted tuple of element indices."""
    best = None
    Sidx = [idx[s] for s in S]
    for g in els:
        gi = mat_inv(g)
        t = tuple(sorted(idx[mat_mul(mat_mul(g, s), gi)] for s in S))
        if best is None or t < best:
            best = t
    return best


if __name__ == "__main__":
    els, idx = group()
    print("SL(2,17) order", len(els))
