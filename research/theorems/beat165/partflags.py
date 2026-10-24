# All "partial flag graphs" of finite (spherical) buildings with max degree <= DMAX and diameter <= DMAXD.
# Side A: residues of type J, side B: residues of type K (J u K = S), adjacent iff they meet (in a J n K residue).
# Degree of an A-vertex = P_J(q)/P_{JnK}(q); A-vertices within distance 2k: residues R' with
# delta in X_k = W_J (W_K W_J)^k. Unequal parameters allowed (q_s per generator, constant on classes).
# Groups are enumerated in the Tits representation (numerical), so this is limited to |W| <= ~1e6.
import itertools, math, sys
import numpy as np
from functools import reduce

def coxeter_matrix(typ, n):
    M = [[2] * n for _ in range(n)]
    for i in range(n):
        M[i][i] = 1
    def e(i, j, m):
        M[i][j] = M[j][i] = m
    if typ == 'A':
        for i in range(n - 1): e(i, i + 1, 3)
    elif typ == 'B':
        for i in range(n - 2): e(i, i + 1, 3)
        e(n - 2, n - 1, 4)
    elif typ == 'D':
        for i in range(n - 2): e(i, i + 1, 3)
        e(n - 3, n - 1, 3)
    elif typ == 'E':  # Bourbaki: 1-3-4-5-6(-7-8), 2-4 ; here 0-based: 0-2-3-4-5.., 1-3
        e(0, 2, 3); e(2, 3, 3); e(1, 3, 3)
        for i in range(3, n - 1): e(i, i + 1, 3)
    elif typ == 'F':
        e(0, 1, 3); e(1, 2, 4); e(2, 3, 3)
    elif typ == 'G':
        e(0, 1, 6)
    elif typ == 'I8':
        e(0, 1, 8)
    return M

def tits(M):
    n = len(M)
    B = np.array([[1.0 if i == j else -math.cos(math.pi / M[i][j]) for j in range(n)] for i in range(n)])
    gens = []
    for i in range(n):
        S = np.eye(n); S[i, :] -= 2 * B[i, :]
        gens.append(S)
    return gens

def key(A):
    return tuple(np.round(A, 5).flatten().tolist())

def enumerate_group(M, limit=2_000_000):
    gens = tits(M); n = len(M)
    e = np.eye(n)
    elems = {key(e): (e, ())}
    frontier = [(e, ())]
    while frontier:
        nf = []
        for A, w in frontier:
            for i, g in enumerate(gens):
                B = A @ g; k = key(B)
                if k not in elems:
                    elems[k] = (B, w + (i,)); nf.append((B, w + (i,)))
        frontier = nf
        if len(elems) > limit:
            raise RuntimeError('group too big')
    return gens, elems

def run(typ, n, qs, DMAX=16, DMAXD=5, verbose=False):
    M = coxeter_matrix(typ, n)
    gens, elems = enumerate_group(M)
    # weighted length: q-weight of each element = prod q_s over a reduced word (BFS words are reduced)
    wt = {k: reduce(lambda a, i: a * qs[i], w, 1) for k, (A, w) in elems.items()}
    total = sum(wt.values())
    S = list(range(n))
    def parab(I):
        I = set(I)
        return [k for k, (A, w) in elems.items() if set(w) <= I]
    mat = {k: A for k, (A, w) in elems.items()}
    P = {}
    def PJ(I):
        I = tuple(sorted(I))
        if I not in P:
            P[I] = sum(wt[k] for k in parab(I))
        return P[I]
    out = []
    for r in range(1, n + 1):
        for J in itertools.combinations(S, r):
            for r2 in range(1, n + 1):
                for K in itertools.combinations(S, r2):
                    if set(J) | set(K) != set(S) or J > K:
                        continue
                    JK = tuple(sorted(set(J) & set(K)))
                    dA = PJ(J) // PJ(JK); dB = PJ(K) // PJ(JK)
                    if max(dA, dB) > DMAX or J == K:
                        continue
                    nA = total // PJ(J); nB = total // PJ(K)
                    # diameter: smallest k with X_k = W (A side) and same from B
                    WJ = [mat[k] for k in parab(J)]; WK = [mat[k] for k in parab(K)]
                    def steps(W1, W2):
                        X = {key(A): A for A in W1}
                        d = 0
                        while len(X) < len(elems):
                            Y = {}
                            for A in X.values():
                                for b in W2:
                                    B = A @ b; Y[key(B)] = B
                            X2 = {}
                            for A in Y.values():
                                for c in W1:
                                    B = A @ c; X2[key(B)] = B
                            X = X2; d += 2
                            if d > 12: return 99
                        return d
                    eA = steps(WJ, WK); eB = steps(WK, WJ)
                    diam = max(eA, eB)
                    # opposite-side eccentricity is at most the same-side one + 1
                    if diam <= DMAXD + 1:
                        out.append((typ + str(n), qs, J, K, dA, dB, nA, nB, eA, eB))
    return out

if __name__ == '__main__':
    pp = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]
    res = []
    types = [('A', n) for n in range(2, 8)] + [('B', n) for n in range(2, 7)] + [('D', n) for n in range(4, 7)] \
        + [('E', 6), ('F', 4), ('G', 2)]
    for typ, n in types:
        for q in pp:
            for qs in {tuple([q] * n)} | ({tuple([q] * (n - 1) + [q * q])} if typ == 'B' else set()) \
                    | ({tuple([q * q] * (n - 1) + [q])} if typ == 'B' else set()) \
                    | ({tuple([q * q] * (n - 1) + [q ** 3])} if typ == 'B' else set()) \
                    | ({(q, q ** 3)} if typ == 'G' else set()) | ({(q, q, q * q, q * q)} if typ == 'F' else set()):
                try:
                    r = run(typ, n, list(qs))
                except RuntimeError:
                    continue
                res += r
                if min(qs) ** 1 > 16: break
    res.sort(key=lambda t: -(t[6] + t[7]))
    print('type q-params J K degA degB nA nB eccA(same side) eccB(same side); kept if same-side ecc <= 6')
    for t in res:
        if max(t[8], t[9]) <= 4:
            print('D<=5', t)
    print('--- same-side ecc 6 (D = 6 or 7), top 15 by size')
    for t in [t for t in res if max(t[8], t[9]) == 6][:15]:
        print(t)
