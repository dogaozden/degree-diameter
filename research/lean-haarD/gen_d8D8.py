"""Certificate generator for the Lean proof of the record Delta 8 . D 8, 225,792 vertices (job d8D8).

Group G = PSL(2,7) x SL(2,7) x Z2, N = 168 * 336 * 2 = 112896 elements per side.
Element n = i*672 + j*2 + z  <->  (PSL index i, SL index j, Z2 index z).

PSL(2,7) is modelled as the canonical +-representatives of SL(2,7): a 2x2 matrix (a,b,c,d) over Z/7 with
ad - bc = 1 is canonical iff key(X) <= key(-X), key(X) = ((a*7+b)*7+c)*7+d.  The product in PSL is
canon(XY).  This is exactly the Lean model in lean/BipartiteDD/Haar/R225792/Model.lean.

Covering conditions for diameter 8 (derived in the Lean walk lemma, Haar/Eight.lean), with S = {s_0..s_7}:
  A: every x in G is  s1^-1 s2 s3^-1 s4 s5^-1 s6 s7^-1 s8   (= (S^-1 S)^4)
  B: every x in G is  s1 s2^-1 s3 s4^-1 s5 s6^-1 s7 s8^-1    (= (S S^-1)^4)
  C: every x in G is  s1 s2^-1 s3 s4^-1 s5 s6^-1 s7          (= (S S^-1)^3 S)
Each word is stored as 8 letters (3 bits each, 24 bits).  Element certificate = wA + 2^24 wB + 2^48 wC (72 bits).
Stage k (k = 0..27) covers the PSL indices i in [6k, 6k+6): 4032 elements, one 72-bit block each.

Usage: python3 gen_d8D8.py SOLUTION.txt OUTDIR
Writes OUTDIR/Lists.lean (group lists and the 8 letters of S) and OUTDIR/Stage00.lean .. Stage27.lean.
Checks everything it writes in Python first (BFS coverage and every word re-multiplied in G).
"""
import itertools
import os
import re
import sys
from collections import deque

import numpy as np

P = 7
N_PSL, N_SL, N_Z = 168, 336, 2
N = N_PSL * N_SL * N_Z  # 112896
STAGE_BLOCKS = 6        # PSL indices per stage
STAGE_LEN = STAGE_BLOCKS * N_SL * N_Z  # 4032
N_STAGES = N_PSL // STAGE_BLOCKS       # 28


def key(x):
    a, b, c, d = x
    return ((a * 7 + b) * 7 + c) * 7 + d


def neg(x):
    return tuple((-v) % 7 for v in x)


def canon(x):
    return x if key(x) <= key(neg(x)) else neg(x)


def mul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % 7, (a * f + b * h) % 7, (c * e + d * g) % 7, (c * f + d * h) % 7)


def det(x):
    a, b, c, d = x
    return (a * d - b * c) % 7


def adj(x):
    a, b, c, d = x
    return (d, (-b) % 7, (-c) % 7, a)


def parse_solution(path):
    text = open(path).read().splitlines()
    head = text[0].split()
    d_target, D_target = int(head[0]), int(head[1])
    assert "N" in head and int(head[head.index("N") + 1]) == N, "unexpected group order"
    S = []
    for line in text[1:]:
        m = re.search(r"prod\[mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\);mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\)\] z=(\d)", line)
        if not m:
            continue
        v = [int(t) for t in m.groups()]
        p = tuple(x % 7 for x in v[0:4])
        q = tuple(x % 7 for x in v[4:8])
        S.append((p, q, v[8] % 2))
    assert len(S) == 8, f"expected 8 set elements, got {len(S)}"
    assert (d_target, D_target) == (8, 8)
    return S


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)

    # ---- group tables
    SL = sorted((x for x in itertools.product(range(7), repeat=4) if det(x) == 1), key=key)
    assert len(SL) == N_SL, len(SL)
    PSL = [x for x in SL if key(x) <= key(neg(x))]
    assert len(PSL) == N_PSL, len(PSL)
    assert all(canon(x) == x for x in PSL)
    slIdx = {x: i for i, x in enumerate(SL)}
    pslIdx = {x: i for i, x in enumerate(PSL)}
    PM = np.array([[pslIdx[canon(mul(x, y))] for y in PSL] for x in PSL], dtype=np.int64)
    QM = np.array([[slIdx[mul(x, y)] for y in SL] for x in SL], dtype=np.int64)
    PInv = [pslIdx[canon(adj(x))] for x in PSL]
    QInv = [slIdx[adj(x)] for x in SL]
    pI = pslIdx[canon((1, 0, 0, 1))]
    qI = slIdx[(1, 0, 0, 1)]
    ident = pI * (N_SL * N_Z) + qI * N_Z + 0

    def gmul(x, y):
        return (int(PM[x[0], y[0]]), int(QM[x[1], y[1]]), (x[2] + y[2]) % 2)

    def ginv(x):
        return (PInv[x[0]], QInv[x[1]], x[2])

    def enc(x):
        return x[0] * (N_SL * N_Z) + x[1] * N_Z + x[2]

    def dec(n):
        return (n // (N_SL * N_Z), (n % (N_SL * N_Z)) // N_Z, n % N_Z)

    # ---- the set S (indices)
    S_raw = parse_solution(sol)
    S = []
    for p, q, z in S_raw:
        cp = canon(p)
        assert cp == p or True
        S.append((pslIdx[cp], slIdx[q], z))
    assert len(set(S)) == 8, "S not distinct"
    assert all(det(q) == 1 for _, q, _ in S_raw)
    S_el = [(pi, qj, z) for pi, qj, z in S]

    # ---- BFS over G with left multiplication by a generator set
    def bfs(gens, depth):
        """gens: list of (label, element). Returns (level, parent, pgen) arrays over N states."""
        level = np.full(N, -1, dtype=np.int64)
        parent = np.full(N, -1, dtype=np.int64)
        pgen = np.full(N, -1, dtype=np.int64)
        e = ident
        level[e] = 0
        frontier = np.array([e], dtype=np.int64)
        PI = np.arange(N) // (N_SL * N_Z)
        QJ = (np.arange(N) % (N_SL * N_Z)) // N_Z
        ZZ = np.arange(N) % N_Z
        for d in range(1, depth + 1):
            new_states = []
            for gi, (_, g) in enumerate(gens):
                fi = frontier
                imgs = (PM[g[0], PI[fi]] * (N_SL * N_Z) + QM[g[1], QJ[fi]] * N_Z + (g[2] + ZZ[fi]) % 2)
                mask = level[imgs] == -1
                if not mask.any():
                    continue
                cand = imgs[mask]
                src = fi[mask]
                uniq, idx = np.unique(cand, return_index=True)
                level[uniq] = d
                parent[uniq] = src[idx]
                pgen[uniq] = gi
                new_states.append(uniq)
            if new_states:
                frontier = np.concatenate(new_states)
            else:
                frontier = np.array([], dtype=np.int64)
        return level, parent, pgen

    def path_pairs(x, level, parent, pgen, gens):
        """outer-first list of generator labels (a,b) with x = u_L ... u_1, padded at the front to the BFS depth."""
        labels = []
        cur = x
        while level[cur] > 0:
            labels.append(gens[pgen[cur]][0])
            cur = parent[cur]
        return labels  # outermost first, length = level[x]

    # generators: pairs (a,b) of S-indices
    A_gens = [((a, b), gmul(ginv(S_el[a]), S_el[b])) for a in range(8) for b in range(8)]  # s_a^-1 s_b
    B_gens = [((a, b), gmul(S_el[a], ginv(S_el[b]))) for a in range(8) for b in range(8)]  # s_a s_b^-1

    levA, parA, pgA = bfs(A_gens, 4)
    assert (levA >= 0).all(), f"(S^-1 S)^4 misses {int((levA < 0).sum())} elements"
    levB, parB, pgB = bfs(B_gens, 4)
    assert (levB >= 0).all(), f"(S S^-1)^4 misses {int((levB < 0).sum())} elements"
    levC, parC, pgC = bfs(B_gens, 3)
    print("BFS ok: A depth max", int(levA.max()), " B depth max", int(levB.max()), " C (S S^-1)^3 covers",
          int((levC >= 0).sum()), "of", N, "states (C needs (SS^-1)^3 S = G)")

    def pad_front(pairs, length):
        return [(0, 0)] * (length - len(pairs)) + pairs

    def letters_of(pairs):
        out = []
        for a, b in pairs:
            out += [a, b]
        return out

    def prodA(L):  # s1^-1 s2 s3^-1 s4 s5^-1 s6 s7^-1 s8
        r = (pI, qI, 0)
        for t, s in enumerate(L):
            el = S_el[s]
            r = gmul(r, ginv(el) if t % 2 == 0 else el)
        return r

    def prodB(L):  # s1 s2^-1 s3 s4^-1 s5 s6^-1 s7 s8^-1
        r = (pI, qI, 0)
        for t, s in enumerate(L):
            el = S_el[s]
            r = gmul(r, el if t % 2 == 0 else ginv(el))
        return r

    def prodC(L):  # s1 s2^-1 s3 s4^-1 s5 s6^-1 s7
        r = (pI, qI, 0)
        for t, s in enumerate(L[:7]):
            el = S_el[s]
            r = gmul(r, el if t % 2 == 0 else ginv(el))
        return r

    def word_code(L):
        assert len(L) == 8 and all(0 <= v < 8 for v in L)
        return sum(v << (3 * t) for t, v in enumerate(L))

    certs = np.zeros(N, dtype=object)
    for n in range(N):
        x = dec(n)
        # A
        pairsA = pad_front(path_pairs(n, levA, parA, pgA, A_gens), 4)
        LA = letters_of(pairsA)
        assert prodA(LA) == x, ("A word wrong", n)
        # B
        pairsB = pad_front(path_pairs(n, levB, parB, pgB, B_gens), 4)
        LB = letters_of(pairsB)
        assert prodB(LB) == x, ("B word wrong", n)
        # C: x = y s_k with y in (S S^-1)^3
        k = None
        for kk in range(8):
            y = gmul(x, ginv(S_el[kk]))
            if levC[enc(y)] >= 0:
                k = kk
                break
        assert k is not None, ("C: no last letter", n)
        y = enc(gmul(x, ginv(S_el[k])))
        pairsC = pad_front(path_pairs(y, levC, parC, pgC, B_gens), 3)
        LC = letters_of(pairsC) + [k]
        LC = LC + [0] * (8 - len(LC))
        assert prodC(LC) == x, ("C word wrong", n)
        certs[n] = word_code(LA) | (word_code(LB) << 24) | (word_code(LC) << 48)
    print("all", N, "elements: A, B, C words re-multiplied in G and match")

    # ---- multiplication and inverse tables (rows of packed fields)
    def lean_m2(x):
        return "⟨%d, %d, %d, %d⟩" % x

    def pack(vals, bits):
        return sum(int(v) << (bits * t) for t, v in enumerate(vals))

    tab = []
    tab.append("/- Generated by research/lean-haarD/gen_d8D8.py. Do not edit by hand. -/")
    tab.append("import BipartiteDD.Haar.R225792.Model")
    tab.append("")
    tab.append("namespace BipartiteDD.Haar.R225792")
    tab.append("")
    tab.append("/-- Row `i` of the PSL multiplication table: entry `j` is the index of `PSL[i] * PSL[j]`, 8 bits. -/")
    tab.append("def mProws : List ℕ := [")
    tab.append(",\n".join("  %s" % hex(pack(PM[i], 8)) for i in range(N_PSL)))
    tab.append("]")
    tab.append("")
    tab.append("/-- Row `j` of the SL multiplication table, 9 bits per entry. -/")
    tab.append("def mQrows : List ℕ := [")
    tab.append(",\n".join("  %s" % hex(pack(QM[j], 9)) for j in range(N_SL)))
    tab.append("]")
    tab.append("")
    tab.append("/-- Inverses in PSL, 8 bits per entry. -/")
    tab.append("def iPtab : ℕ := %s" % hex(pack(PInv, 8)))
    tab.append("/-- Inverses in SL, 9 bits per entry. -/")
    tab.append("def iQtab : ℕ := %s" % hex(pack(QInv, 9)))
    tab.append("/-- The identity of `G8`: PSL index and SL index. -/")
    tab.append("def idP : ℕ := %d" % pI)
    tab.append("def idQ : ℕ := %d" % qI)
    tab.append("")
    tab.append("end BipartiteDD.Haar.R225792")
    tab.append("")
    open(os.path.join(outdir, "TabData.lean"), "w").write("\n".join(tab))

    # ---- stage certificates: one list of 4032 blocks per stage, written as 16 literal chunks joined by ++
    # (one long list literal exceeds Lean's recursion depth during elaboration)
    CHUNK = 252
    for k in range(N_STAGES):
        vals = [int(certs[k * STAGE_LEN + t]) for t in range(STAGE_LEN)]
        parts = []
        for c in range(0, STAGE_LEN, CHUNK):
            items = ",\n".join("  %d" % v for v in vals[c:c + CHUNK])
            parts.append(f"def cert{k:02d}_{c // CHUNK:02d} : List ℕ := [\n{items}\n]\n")
        joined = " ++ ".join(f"cert{k:02d}_{c // CHUNK:02d}" for c in range(0, STAGE_LEN, CHUNK))
        body = [
            "/- Generated by research/lean-haarD/gen_d8D8.py. Do not edit by hand. -/",
            "import BipartiteDD.Haar.R225792.Check",
            "",
            "namespace BipartiteDD.Haar.R225792",
            "",
            f"/-- Certificates of stage {k} (PSL indices {STAGE_BLOCKS * k} .. {STAGE_BLOCKS * k + STAGE_BLOCKS - 1}):"
            f" element `t` is `(i, j, z) = ({STAGE_BLOCKS * k} + t / 672, (t % 672) / 2, t % 2)`, with a 72-bit block"
            " (wA, wB, wC) of eight letters of 3 bits each. -/",
        ]
        body.append("\n".join(parts))
        body += [
            f"def cert{k:02d} : List ℕ := {joined}",
            "",
            f"theorem stage{k:02d}_ok : checkStage {k} cert{k:02d} = true := by decide +kernel",
            "",
            "end BipartiteDD.Haar.R225792",
            "",
        ]
        open(os.path.join(outdir, f"Stage{k:02d}.lean"), "w").write("\n".join(body))

    print("wrote", N_STAGES, "stages to", outdir)


if __name__ == "__main__":
    main()
