"""Independent check of Theorems 1, 2 (and the 'Equivalently' formula) on thin buildings (Coxeter complexes),
for crystallographic and non-crystallographic types. Chambers = W, delta(u,v) = u^-1 v, J-residue of u = u W_J.
Flag graph: vertices = cosets u W_I1 and u W_I2, adjacent iff they intersect. BFS vs block-product formula."""
import numpy as np, itertools, sys
from collections import deque

def coxeter_matrix(t, n):
    M = [[2]*n for _ in range(n)]
    for i in range(n): M[i][i] = 1
    def b(i, j, m): M[i][j] = M[j][i] = m
    if t == 'A':
        for i in range(n-1): b(i, i+1, 3)
    elif t == 'B':
        for i in range(n-2): b(i, i+1, 3)
        b(n-2, n-1, 4)
    elif t == 'D':
        for i in range(n-2): b(i, i+1, 3)
        b(n-3, n-1, 3)
    elif t == 'E':
        # Bourbaki: 1-3-4-5-...-n, 2-4  (0-based: 0-2-3-4..., 1-3)
        ch = [0, 2] + list(range(3, n))
        for a, c in zip(ch, ch[1:]): b(a, c, 3)
        b(1, 3, 3)
    elif t == 'F':
        b(0, 1, 3); b(1, 2, 4); b(2, 3, 3)
    elif t == 'H':
        b(0, 1, 5)
        for i in range(1, n-1): b(i, i+1, 3)
    elif t == 'I':
        pass
    return M

def group(M):
    n = len(M)
    G = np.array([[-np.cos(np.pi / M[i][j]) for j in range(n)] for i in range(n)])
    S = []
    for i in range(n):
        A = np.eye(n)
        for j in range(n):
            A[i, j] -= 2 * G[i, j]   # s_i(alpha_j) = alpha_j - 2B(a_i,a_j) a_i ; column j = image of alpha_j
        S.append(A)
    v0 = np.linalg.solve(G, np.ones(n))
    key = lambda A: tuple(np.round(A @ v0, 6))
    elems = {key(np.eye(n)): np.eye(n)}; length = {key(np.eye(n)): 0}
    fr = [np.eye(n)]
    while fr:
        nf = []
        for A in fr:
            ka = key(A)
            for s in S:
                B = s @ A; kb = key(B)
                if kb not in elems:
                    elems[kb] = B; length[kb] = length[ka] + 1; nf.append(B)
        fr = nf
    return S, elems, length, key

def colour(M):
    n = len(M); c = [-1]*n; c[0] = 0; st = [0]
    while st:
        x = st.pop()
        for y in range(n):
            if y != x and M[x][y] != 2 and c[y] < 0: c[y] = 1 - c[x]; st.append(y)
    return [[i for i in range(n) if c[i] == k] for k in (0, 1)]

def parabolic(S, I, n):
    els = [np.eye(n)]
    for i in I:
        els = els + [s_ @ S[i] for s_ in els]
    return els

def run(t, n, m=None):
    M = coxeter_matrix(t, n) if t != 'I' else [[1, m], [m, 1]]
    n = len(M)
    S, elems, length, key = group(M)
    I = colour(M)
    keys = list(elems)
    idx = {k: a for a, k in enumerate(keys)}
    N = max(length.values())
    WI = [parabolic(S, I[0], n), parabolic(S, I[1], n)]
    # coset ids: for each element w and class K, id of w W_K
    cos = [dict(), dict()]
    for K in (0, 1):
        cid = 0
        for k in keys:
            if k in cos[K]: continue
            A = elems[k]
            for u in WI[K]:
                cos[K][key(A @ u)] = cid
            cid += 1
    nv = [max(cos[K].values()) + 1 for K in (0, 1)]
    # adjacency: vertex (K, id)
    adj = {}
    for k in keys:
        a = (0, cos[0][k]); b = (1, cos[1][k])
        adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
    res = []
    lit_bad = 0; cor_bad = 0; thm2_bad = 0
    h = 2 * N // n
    ecc = []
    for J in (0, 1):
        # BFS from the coset e W_J
        src = (J, cos[J][key(np.eye(n))])
        dist = {src: 0}; dq = deque([src])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in dist: dist[y] = dist[x] + 1; dq.append(y)
        assert len(dist) == nv[0] + nv[1]
        ecc.append(max(dist.values()))
        # block products X_m = W_J0 ... W_J(m-1)
        level = {}
        X = {key(u): u for u in WI[J]}
        for kk in X: level[kk] = 1
        mm = 1
        while len(level) < len(keys):
            Jm = J if mm % 2 == 0 else 1 - J   # 0-based: factor index mm has type J if mm even
            newX = {}
            for kk, A in X.items():
                for u in WI[Jm]:
                    B = A @ u; kb = key(B)
                    newX[kb] = B
            mm += 1
            for kb in newX:
                if kb not in level: level[kb] = mm
            X = newX
        for k in keys:
            for K in (0, 1):
                d = dist[(K, cos[K][k])]
                mJ = level[k]
                # Theorem 2 main formula: least l with parity [J!=K] and l+1 >= mJ
                par = 0 if J == K else 1
                l = mJ - 1
                if l % 2 != par: l += 1
                if l != d: thm2_bad += 1
                # literal 'Equivalently': d = m - [J_m = K], J_m 0-based (J if m even)
                Jm_lit = J if mJ % 2 == 0 else 1 - J
                if mJ - (1 if Jm_lit == K else 0) != d: lit_bad += 1
                Jm1 = J if (mJ - 1) % 2 == 0 else 1 - J
                if mJ - (1 if Jm1 == K else 0) != d: cor_bad += 1
    name = f"{t}{n}" if t != 'I' else f"I2({m})"
    print(f"{name:7s} |W|={len(keys):6d} N={N:3d} h={h:3d} classes={len(I[0])}+{len(I[1])} vertices={nv[0]}+{nv[1]} "
          f"ecc from I1,I2 = {ecc}  Thm2 mismatches={thm2_bad}  'Equivalently' as written mismatches={lit_bad}  corrected={cor_bad}")
    sys.stdout.flush()

if __name__ == "__main__":
  for args in [('A',2),('A',3),('A',4),('A',5),('B',2),('B',3),('B',4),('D',4),('D',5),('F',4),('H',3),('H',4),('E',6)]:
      run(*args)
  for m in [5,7,8,9,10,12]:
    run('I', 2, m)
