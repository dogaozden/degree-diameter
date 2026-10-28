"""Card c6: 3 levels of type H over Q4(3), all transitions non-friendly, freed sets R_j of size s,
B-hubs / A-hubs (one slot per level each), Y 2-regular bipartite between hubs. Anneal on M, R, slots, Y
minimising the number of ordered vertex pairs at distance > 5.
Usage: python3 anneal.py s iters seed [out.json]"""
import sys, os, json, math, random
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'theorems', 'd5gq'))
from gqlib import Q4
G = Q4(3)
NP, NL = G.np, G.nl          # 40, 40
PER = NP + NL                 # 80
L = 3
NB = L * PER                  # 240

BASE = np.zeros((NB, NB), dtype=np.float32)
for j in range(L):
    for l, pts in enumerate(G.lines):
        for p in pts:
            BASE[j * PER + p, j * PER + NP + l] = 1
            BASE[j * PER + NP + l, j * PER + p] = 1


def build_adj(s, M, Bs, As, alpha):
    n = NB + 2 * s
    A = np.zeros((n, n), dtype=np.float32)
    A[:NB, :NB] = BASE
    for j in range(L):
        j2 = (j + 1) % L
        R = set(Bs[j].tolist())
        for p in range(NP):
            if p in R:
                continue
            u = j * PER + p; v = j2 * PER + NP + M[j][p]
            A[u, v] = A[v, u] = 1
    for h in range(s):
        for j in range(L):
            u = NB + h; v = j * PER + Bs[j][h]
            A[u, v] = A[v, u] = 1
    for g in range(s):
        for j in range(L):
            j2 = (j + 1) % L
            u = NB + s + g; v = j2 * PER + NP + M[j][As[j][g]]
            A[u, v] = A[v, u] = 1
    if s >= 2:
        for h in range(s):
            for g in {alpha[h], alpha[(h + 1) % s]}:
                u = NB + h; v = NB + s + g
                A[u, v] = A[v, u] = 1
    elif s == 1:
        A[NB, NB + 1] = A[NB + 1, NB] = 1
    return A


def bad_pairs(A):
    n = A.shape[0]
    P = A + np.eye(n, dtype=np.float32)
    X = P
    for _ in range(4):
        X = ((X @ P) > 0).astype(np.float32)
    return int(n * n - np.count_nonzero(X))


def bad_pairs_vertices(A):
    return bad_pairs(A)


def random_state(s, rng):
    M = [np.array(rng.sample(range(NL), NP)) for _ in range(L)]
    Bs = []; As = []
    for j in range(L):
        R = rng.sample(range(NP), s)
        Bs.append(np.array(R))
        As.append(np.array(rng.sample(R, s)))
    alpha = rng.sample(range(s), s) if s else []
    return M, Bs, As, alpha


def anneal(s, iters, rng, T0=1.5, T1=0.05, state=None):
    if state is None:
        state = random_state(s, rng)
    M, Bs, As, alpha = [x for x in state]
    M = [np.array(m) for m in M]; Bs = [np.array(b) for b in Bs]; As = [np.array(a) for a in As]
    alpha = list(alpha)
    cur = bad_pairs(build_adj(s, M, Bs, As, alpha))
    best = (cur, [m.copy() for m in M], [b.copy() for b in Bs], [a.copy() for a in As], list(alpha))
    for it in range(iters):
        if cur == 0:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        mv = rng.random()
        j = rng.randrange(L)
        undo = None
        if mv < 0.35:
            p1, p2 = rng.sample(range(NP), 2)
            M[j][p1], M[j][p2] = M[j][p2], M[j][p1]
            undo = ('M', j, p1, p2)
        elif mv < 0.5 and s < NP:
            x = int(Bs[j][rng.randrange(s)])
            cand = [y for y in range(NP) if y not in set(Bs[j].tolist())]
            y = rng.choice(cand)
            oldB = Bs[j].copy(); oldA = As[j].copy()
            Bs[j][Bs[j] == x] = y; As[j][As[j] == x] = y
            undo = ('R', j, oldB, oldA)
        elif mv < 0.7 and s >= 2:
            h1, h2 = rng.sample(range(s), 2)
            Bs[j][h1], Bs[j][h2] = Bs[j][h2], Bs[j][h1]
            undo = ('B', j, h1, h2)
        elif mv < 0.9 and s >= 2:
            g1, g2 = rng.sample(range(s), 2)
            As[j][g1], As[j][g2] = As[j][g2], As[j][g1]
            undo = ('A', j, g1, g2)
        elif s >= 3:
            g1, g2 = rng.sample(range(s), 2)
            alpha[g1], alpha[g2] = alpha[g2], alpha[g1]
            undo = ('Y', g1, g2)
        if undo is None:
            continue
        new = bad_pairs(build_adj(s, M, Bs, As, alpha))
        d = new - cur
        if d <= 0 or rng.random() < math.exp(-d / T):
            cur = new
            if cur < best[0]:
                best = (cur, [m.copy() for m in M], [b.copy() for b in Bs], [a.copy() for a in As], list(alpha))
        else:
            k = undo[0]
            if k == 'M':
                _, j, p1, p2 = undo; M[j][p1], M[j][p2] = M[j][p2], M[j][p1]
            elif k == 'R':
                _, j, oldB, oldA = undo; Bs[j] = oldB; As[j] = oldA
            elif k == 'B':
                _, j, h1, h2 = undo; Bs[j][h1], Bs[j][h2] = Bs[j][h2], Bs[j][h1]
            elif k == 'A':
                _, j, g1, g2 = undo; As[j][g1], As[j][g2] = As[j][g2], As[j][g1]
            elif k == 'Y':
                _, g1, g2 = undo; alpha[g1], alpha[g2] = alpha[g2], alpha[g1]
    return best


if __name__ == '__main__':
    s = int(sys.argv[1]); iters = int(sys.argv[2]); seed = int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else None
    rng = random.Random(seed)
    best = anneal(s, iters, rng)
    print(json.dumps({'s': s, 'seed': seed, 'bad': best[0]}))
    if out:
        with open(out, 'w') as f:
            json.dump({'s': s, 'bad': best[0], 'M': [m.tolist() for m in best[1]],
                       'Bs': [b.tolist() for b in best[2]], 'As': [a.tolist() for a in best[3]],
                       'alpha': best[4]}, f)
