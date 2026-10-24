# Ball sizes in the bipartite "flag graph" of a building of Coxeter type M with all thickness q.
# Vertex classes: residues of type J (side A) and type K (side B), J, K each a set of pairwise commuting
# generators with J u K = S, J n K = empty. A-vertices within distance 2k of x are the J-residues R' with
# delta(R_x, R') in X_k = W_J (W_K W_J)^k; their number is sum_{w in X_k} q^len(w) / P_J(q).
# Elements are stored as matrices of the geometric (Tits) representation, rounded, so lengths are exact
# BFS distances in the Cayley graph. Usage: python3 coxball.py
import itertools, math, sys
import numpy as np

def tits(M):
    n = len(M)
    B = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            m = M[i][j]
            B[i, j] = 1.0 if i == j else (-1.0 if m == 0 else -math.cos(math.pi / m))
    gens = []
    for i in range(n):
        S = np.eye(n)
        for j in range(n):
            S[i, j] -= 2 * B[i, j]
        gens.append(S)
    return gens

def key(A):
    return tuple(np.round(A, 6).flatten().tolist())

def ball_sizes(M, J, K, q, kmax=2, maxlen=None):
    n = len(M)
    gens = tits(M)
    # BFS over the Cayley graph up to the needed length
    L = (len(J) + len(K)) * (kmax + 1) if maxlen is None else maxlen
    e = np.eye(n)
    length = {key(e): 0}
    mats = {key(e): e}
    frontier = [e]
    for l in range(1, L + 1):
        nf = []
        for A in frontier:
            for g in gens:
                B = A @ g
                k = key(B)
                if k not in length:
                    length[k] = l; mats[k] = B; nf.append(B)
        frontier = nf
    def par(I):  # elements of the standard parabolic W_I (I pairwise commuting)
        out = []
        for r in range(len(I) + 1):
            for c in itertools.combinations(I, r):
                A = np.eye(n)
                for i in c:
                    A = A @ gens[i]
                out.append(A)
        return out
    WJ, WK = par(J), par(K)
    PJ = sum(q ** length[key(A)] for A in WJ)
    X = {key(A): A for A in WJ}
    res = []
    for k in range(1, kmax + 1):
        Y = {}
        for A in X.values():
            for b in WK:
                for c in WJ:
                    B = A @ b @ c
                    Y[key(B)] = B
        X = Y
        miss = [kk for kk in X if kk not in length]
        if miss:
            raise SystemExit('increase maxlen')
        tot = sum(q ** length[kk] for kk in X)
        res.append((2 * k, len(X), tot // PJ if tot % PJ == 0 else tot / PJ))
    return PJ, res

def cyc4(a, b, c, d):  # 4-cycle 0-1-2-3-0 with labels (01,12,23,30); 2 = no edge, 0 = infinity
    M = [[1] * 4 for _ in range(4)]
    def s(i, j, m):
        M[i][j] = M[j][i] = m
    s(0, 1, a); s(1, 2, b); s(2, 3, c); s(3, 0, d); s(0, 2, 2); s(1, 3, 2)
    return M

if __name__ == '__main__':
    q = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    cases = {
        'A4 (path, labels 3,3,3; 30 = 2)': cyc4(3, 3, 3, 2),
        'A~3 (4-cycle, all 3)': cyc4(3, 3, 3, 3),
        'C~3 (path 4,3,4)': cyc4(4, 3, 4, 2),
        'B4/C4 (path 3,3,4)': cyc4(3, 3, 4, 2),
        'F4 (path 3,4,3)': cyc4(3, 4, 3, 2),
        'cycle 3,3,3,4': cyc4(3, 3, 3, 4),
        'cycle 3,4,3,4': cyc4(3, 4, 3, 4),
        'cycle 4,4,4,4': cyc4(4, 4, 4, 4),
        'path 3,3,6': cyc4(3, 3, 6, 2),
        'cycle 3,3,3,6': cyc4(3, 3, 3, 6),
    }
    J, K = [0, 2], [1, 3]
    for name, M in cases.items():
        PJ, res = ball_sizes(M, J, K, q, kmax=2)
        print(f'{name:34s} q={q} P_J={PJ}  ' + '  '.join(f'r{r}: |X|={x} A-vertices={v}' for r, x, v in res))
