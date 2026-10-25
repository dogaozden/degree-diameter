"""Independent check of cyclobound.py: in actual groups G = Z_p x|_r Z_k, the number of distinct ball elements in each
fibre J (for every start side and target side) must be at most |W_J| computed in the universal group, for the same
j-pattern.  At Delta=3 the set S is fixed by j (normal form a1 = 0, a2 = 1); at Delta=4 a3 is random.
The G-side BFS is written from scratch here (pure Python), not shared with cyclobound.py.
Usage: python3 cyclocheck.py DELTA D NGROUPS [--seed 1]"""
import random
import sys
from collections import defaultdict

import cyclobound
from frob_scan import actions, primes_upto


def g_fibres(p, k, r, S, D):
    """per (start side, target side): dict J -> number of distinct elements (a, J) within distance D."""
    rp = [pow(r, j, p) for j in range(k)]

    def mul(x, y):
        (a, j), (b, l) = x, y
        return ((a + rp[j] * b) % p, (j + l) % k)

    def inv(x):
        a, j = x
        jj = (-j) % k
        return ((-rp[jj] * a) % p, jj)

    Sinv = [inv(s) for s in S]
    out = {}
    for start in (0, 1):
        seen = [set(), set()]
        e = (0, 0)
        seen[start].add(e)
        frontier, side = [e], start
        for _ in range(D):
            nside = 1 - side
            nxt = []
            for g in frontier:
                for i in range(len(S)):
                    h = mul(S[i], g) if side == 0 else mul(Sinv[i], g)   # (g,A) ~ (s g, B); (g,B) ~ (s^-1 g, A)
                    if h not in seen[nside]:
                        seen[nside].add(h)
                        nxt.append(h)
            frontier, side = nxt, nside
        for t in (0, 1):
            cnt = defaultdict(int)
            for (a, J) in seen[t]:
                cnt[J] += 1
            out[(start, t)] = cnt
    return out


def u_fibres(Delta, D, k, o, j):
    """the same counts in the universal group, via cyclobound's BFS (recomputed with fibre bookkeeping)."""
    import numpy as np
    M, f = cyclobound.zeta_powers(o)
    F = Delta - 2
    width = F * f
    eps = []
    for i in range(Delta):
        v = np.zeros(width, dtype=np.int64)
        if i >= 2:
            v[(i - 2) * f] = 1
        eps.append(v)

    def act(P, t):
        t %= o
        out = np.empty_like(P)
        for fi in range(F):
            out[:, fi * f:(fi + 1) * f] = P[:, fi * f:(fi + 1) * f] @ M[t].T
        return out

    res = {}
    for start in (0, 1):
        P = np.zeros((1, width), dtype=np.int64)
        J = np.zeros(1, dtype=np.int64)
        side = start
        seen = [set(), set()]
        seen[side].add(P[0].tobytes() + J[0:1].tobytes())
        for _ in range(D):
            newP, newJ = [], []
            for i in range(Delta):
                if side == 0:
                    newP.append(act(P, j[i]) + eps[i]); newJ.append((J + j[i]) % k)
                else:
                    newP.append(act(P - eps[i], -j[i])); newJ.append((J - j[i]) % k)
            Q, L = np.concatenate(newP), np.concatenate(newJ)
            nside = 1 - side
            keepP, keepJ = [], []
            for row, jj in zip(Q, L):
                key = row.tobytes() + np.int64(jj).tobytes()
                if key not in seen[nside]:
                    seen[nside].add(key); keepP.append(row); keepJ.append(jj)
            P = np.array(keepP) if keepP else np.zeros((0, width), dtype=np.int64)
            J = np.array(keepJ, dtype=np.int64) if keepJ else np.zeros(0, dtype=np.int64)
            side = nside
        for t in (0, 1):
            cnt = defaultdict(int)
            for key in seen[t]:
                cnt[int(np.frombuffer(key[-8:], dtype=np.int64)[0])] += 1
            res[(start, t)] = cnt
    return res


def main():
    Delta, D, ng = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
    rng = random.Random(seed)
    groups = []
    for p in primes_upto(60):
        for k in range(2, 30):
            for r, o in actions(p, k):
                groups.append((p, k, r, o))
    rng.shuffle(groups)
    checked = viol = 0
    for (p, k, r, o) in groups[:ng]:
        j1 = rng.choice([x for x in range(1, k) if x % o])
        js = [rng.randrange(k) for _ in range(Delta - 2)]
        j = (0, j1, *js)
        S = [(0, 0), (0, j1), (1, js[0])] + [(rng.randrange(p), js[i]) for i in range(1, Delta - 2)]
        G = g_fibres(p, k, r, S, D)
        U = u_fibres(Delta, D, k, o, j)
        bad = [(key, J, G[key][J], U[key].get(J, 0)) for key in G for J in G[key] if G[key][J] > U[key].get(J, 0)]
        checked += 1
        viol += bool(bad)
        tight = min(U[key].get(J, 0) - G[key][J] for key in G for J in range(k))
        print(f'Z{p} x|_{r} Z{k} (o={o}) j={j} S={S}: ' + ('VIOLATION ' + str(bad[:3]) if bad else
              f'ok (min slack |W_J| - |ball_J| = {tight})'), flush=True)
    print(f'checked {checked} (group, S) pairs at Delta={Delta} D={D}: {viol} violations')


if __name__ == '__main__':
    main()
