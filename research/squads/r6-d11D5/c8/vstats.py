"""Per-new-vertex statistics of a DM base (plusopt format), for the c8 comparison.
For each new point X (id >= 585) and new line l (id >= 585):
  misses   = opposite-side vertices at base distance >= 5 (= n - opposite 3-ball size)
  ball3    = number of vertices at base distance <= 3 (both sides, incl. itself)
  sg4      = same-side vertices at distance 4 with exactly one walk of length 4 (single geodesic)
  nsw      = switch lines of the vertex (old lines it lost a point on, or lines a moved point left)
  niso     = how many of those switch lines R (line = delta(R)) have C(delta(R)) totally isotropic
  fails    = failing (source, target, coset) triples of anal.py touching the vertex (if FAILS given)
C is recovered from sigma (sigma(p) = delta(C(p)) on old points) and a projective frame.
usage: python3 vstats.py base.in [fails.txt]"""
import sys, re, os
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *          # n0, LINES, d_pt, PTS, IDX, norm, matvec, matinv, pmap, is_W, mul, finv
import numpy as np
from collections import Counter

def mm(A, B):
    return [[ (lambda i, j: __import__('functools').reduce(lambda a, k: a ^ mul[A[i][k]][B[k][j]], range(4), 0))(i, j) for j in range(4)] for i in range(4)]

dinv = [0] * n0
for R in range(n0): dinv[d_pt[R]] = R

def recover_C(sig, n, tries=4000):
    """best projective frame map M agreeing with sigma = delta o C on the most old points (greedy edits break exact C)"""
    import random
    Cp = {p: dinv[sig[p]] for p in range(n0) if sig[p] < n0}          # C(p) on non-exceptional old points
    good = sorted(Cp)
    rng = random.Random(1); best = None
    for _ in range(tries):
        five = rng.sample(good, 5)
        A = [[PTS[five[j]][i] for j in range(4)] for i in range(4)]     # columns v1..v4
        Ai = matinv(A)
        if Ai is None: continue
        mu = matvec(Ai, PTS[five[4]])
        if any(m == 0 for m in mu): continue
        Bm = [[PTS[Cp[five[j]]][i] for j in range(4)] for i in range(4)]
        Bi = matinv(Bm)
        if Bi is None: continue
        nu = matvec(Bi, PTS[Cp[five[4]]])
        if any(v == 0 for v in nu): continue
        d = [mul[nu[i]][finv[mu[i]]] for i in range(4)]
        Dm = [[d[i] if i == j else 0 for j in range(4)] for i in range(4)]
        M = mm(mm(Bm, Dm), Ai)
        C = pmap(M)
        ok = sum(1 for p in good if C[p] == Cp[p])
        if best is None or ok > best[0]:
            best = (ok, M, C)
            if ok == len(good): break
    print(f"frame: M agrees with sigma = delta o C on {best[0]} of {len(good)} old points", file=sys.stderr)
    return best[1], best[2]

def main():
    base = sys.argv[1]; fails_path = sys.argv[2] if len(sys.argv) > 2 else None
    t = open(base).read().split(); n, dg = int(t[0]), int(t[1])
    ln = [sorted(int(x) for x in t[2+l*dg:2+l*dg+dg]) for l in range(n)]
    sig = [int(x) for x in t[2+n*dg:2+n*dg+n]]
    M, C = recover_C(sig, n)
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    swl = [L for L in range(n0) if ln[L] != sorted(LINES[L])]
    # distances
    V = 2 * n
    Bm = np.zeros((V, V), dtype=np.int64)
    for l in range(n):
        for p in ln[l]: Bm[p, n + l] += 1; Bm[n + l, p] += 1
    P = [np.eye(V, dtype=np.int64)]
    for k in range(1, 7): P.append(P[-1] @ Bm)
    dist = np.full((V, V), 99)
    for k in range(6, -1, -1): dist[P[k] > 0] = k
    fails = Counter()
    if fails_path:
        for line in open(fails_path):
            m = re.match(r"\((\d+), (\d+), \(", line)
            if m: fails[int(m.group(1))] += 1; fails[int(m.group(2))] += 1
    rows = []
    newv = list(range(n0, n)) + [n + l for l in range(n0, n)]
    for v in newv:
        is_pt = v < n
        opp = slice(n, V) if is_pt else slice(0, n)
        same = slice(0, n) if is_pt else slice(n, V)
        misses = int((dist[v, opp] >= 5).sum())
        ball3 = int((dist[v] <= 3).sum())
        sg4 = int(((dist[v, same] == 4) & (P[4][v, same] == 1)).sum())
        if is_pt:
            sw = [L for L in swl if v in ln[L]]
        else:
            l = v - n; moved = [p for p in ln[l] if p < n0]
            sw = []
            for p in moved:
                cand = [L for L in swl if p in LINES[L] and p not in ln[L]]
                sw += cand
        niso = sum(1 for L in sw if dinv[L] in S)
        rows.append(dict(kind='pt' if is_pt else 'ln', id=(v if is_pt else v - n), misses=misses, ball3_opp=n - misses,
                         ball3=ball3, sg4=sg4, nsw=len(sw), niso=niso, fails=fails.get(v, 0)))
    print(f"file {base}: n={n} |S|={len(S)} switch lines={len(swl)} recovered C ok")
    print("kind id  misses ball3opp ball3all sg4 nsw niso fails")
    for r in rows:
        print(f"{r['kind']:>3} {r['id']:>4} {r['misses']:>6} {r['ball3_opp']:>8} {r['ball3']:>8} {r['sg4']:>4} {r['nsw']:>3} {r['niso']:>4} {r['fails']:>5}")
    return rows

if __name__ == "__main__":
    main()
