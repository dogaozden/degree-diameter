"""Coxeter-group facts used in the proof (BUILDINGS.md, Theorem 1), checked for every irreducible finite
Coxeter type of rank <= 10 (A_n, B_n, D_n), E6, E7, E8, F4, G2, H3, H4 and I2(m), 5 <= m <= 12.

For each type:
  * N = number of positive roots (closure of the simple roots under the simple reflections),
  * h = order of the Coxeter element s_1 s_2 ... s_r, and the identity N = r h / 2,
  * the 2-colouring I1 | I2 of the Coxeter diagram (a tree), and that each class is pairwise commuting,
  * that both alternating words c1 c2 c1 ... and c2 c1 c2 ... with h blocks (c_j = product of the reflections
    in I_j) are REDUCED words of length N, hence reduced words for the longest element w0,
  * the letter count of the alternating words with fewer blocks (lower bound of Theorem 1).
Geometric representation with B(e_i, e_j) = -cos(pi/m_ij); a word s_{i1}...s_{iL} is reduced iff every
s_{i1}...s_{i(k-1)}(alpha_{ik}) is a positive root.  Floating point with tolerance 1e-9 (roots have
coefficients of size <= ~10 here)."""
import math, itertools, sys

def coxeter_matrix(t, n=None):
    if t == 'A':
        M = [[2 if abs(i - j) == 1 else 1 if i == j else 2 for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                M[i][j] = 1 if i == j else (3 if abs(i - j) == 1 else 2)
        return M
    if t in 'BC':
        M = coxeter_matrix('A', n); M[n - 2][n - 1] = M[n - 1][n - 2] = 4; return M
    if t == 'D':
        M = [[1 if i == j else 2 for j in range(n)] for i in range(n)]
        for i in range(n - 3): M[i][i + 1] = M[i + 1][i] = 3      # path 0..n-3
        for leaf in (n - 2, n - 1): M[n - 3][leaf] = M[leaf][n - 3] = 3
        return M
    if t == 'E':   # Bourbaki: 1-3-4-5-6-7-8 with 2 attached to 4 (0-based: 0-2-3-4-..., 1 attached to 3)
        M = [[1 if i == j else 2 for j in range(n)] for i in range(n)]
        chain = [0, 2] + list(range(3, n))
        for a, b in zip(chain, chain[1:]): M[a][b] = M[b][a] = 3
        M[1][3] = M[3][1] = 3
        return M
    if t == 'F':
        M = coxeter_matrix('A', 4); M[1][2] = M[2][1] = 4; return M
    if t == 'G':
        return [[1, 6], [6, 1]]
    if t == 'H':
        M = coxeter_matrix('A', n); M[0][1] = M[1][0] = 5; return M
    if t == 'I':
        return [[1, n], [n, 1]]
    raise ValueError(t)

def run(name, M):
    r = len(M)
    B = [[-math.cos(math.pi / M[i][j]) for j in range(r)] for i in range(r)]
    def refl(i, v):   # sigma_i(v) = v - 2 B(e_i, v) e_i ; v in simple-root coordinates
        c = 2 * sum(B[i][j] * v[j] for j in range(r))
        w = list(v); w[i] -= c; return tuple(w)
    key = lambda v: tuple(round(x, 7) for x in v)
    # positive roots by closure
    simple = [tuple(1.0 if j == i else 0.0 for j in range(r)) for i in range(r)]
    roots = {key(v): v for v in simple}; frontier = list(simple)
    while frontier:
        nf = []
        for v in frontier:
            for i in range(r):
                u = refl(i, v)
                if key(u) not in roots: roots[key(u)] = u; nf.append(u)
        frontier = nf
    pos = [v for v in roots.values() if all(x > -1e-9 for x in v)]
    neg = [v for v in roots.values() if all(x < 1e-9 for x in v)]
    assert len(pos) + len(neg) == len(roots), "root not of one sign"
    N = len(pos)
    # Coxeter number: order of s_0 s_1 ... s_{r-1} acting on R^r
    def apply_word(word, v):
        for i in reversed(word): v = refl(i, v)
        return v
    cox = list(range(r)); h = None
    for k in range(1, 200):
        if all(max(abs(a - b) for a, b in zip(apply_word(cox * k, e), e)) < 1e-9 for e in simple): h = k; break
    # 2-colouring of the diagram
    col = [-1] * r; col[0] = 0; st = [0]
    while st:
        x = st.pop()
        for y in range(r):
            if y != x and M[x][y] >= 3:
                if col[y] < 0: col[y] = 1 - col[x]; st.append(y)
                assert col[y] != col[x], "diagram not bipartite"
    I = [[i for i in range(r) if col[i] == c] for c in (0, 1)]
    commuting = all(M[a][b] == 2 for c in (0, 1) for a in I[c] for b in I[c] if a != b)
    def is_reduced(word):
        # beta_k = s_{i1}...s_{i(k-1)}(alpha_{ik}) must be positive for all k
        prefix = []
        for i in word:
            beta = apply_word(prefix, simple[i])
            if not all(x > -1e-9 for x in beta): return False
            prefix.append(i)
        return True
    res = []
    for start in (0, 1):
        word = []
        for b in range(h): word += I[(start + b) % 2]
        red = is_reduced(word)
        # also: the product sends every positive root to a negative root (so it is w0)
        allneg = all(all(x < 1e-9 for x in apply_word(word, v)) for v in pos)
        res.append((len(word), red, allneg))
    # letter counts of alternating words with fewer blocks (lower bound)
    shorter = {}
    for start in (0, 1):
        shorter[start] = [sum(len(I[(start + b) % 2]) for b in range(m)) for m in (h - 1, h - 2)] if h >= 2 else []
    ok = (h is not None and 2 * N == r * h and commuting and all(L == N and red and an for (L, red, an) in res)
          and all(max(shorter[s][:1]) < N for s in (0, 1)))
    print(f"{name:6s} r={r:2d} N={N:3d} h={h:3d} rh/2={r*h//2:3d} classes={len(I[0])}+{len(I[1])} "
          f"commuting={commuting} h-block words: len={res[0][0]},{res[1][0]} reduced={res[0][1]},{res[1][1]} "
          f"=w0={res[0][2]},{res[1][2]} (h-1)-block letters={shorter[0][0]},{shorter[1][0]} "
          f"{'OK' if ok else 'FAIL'}")
    return ok

types = [('A', n) for n in range(1, 11)] + [('B', n) for n in range(2, 11)] + [('D', n) for n in range(4, 11)] \
        + [('E', 6), ('E', 7), ('E', 8), ('F', 4), ('G', 2), ('H', 3), ('H', 4)] + [('I', m) for m in range(5, 13)]
allok = True
for t, n in types:
    if t == 'A' and n == 1: continue
    name = f"{t}{n}" if t != 'I' else f"I2({n})"
    allok &= run(name, coxeter_matrix(t, n))
print("ALL OK" if allok else "SOME FAILED")
