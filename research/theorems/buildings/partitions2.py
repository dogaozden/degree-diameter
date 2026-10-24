"""§2.1 of BUILDINGS.md for all crystallographic types of rank <= 8 (E8 included), without enumerating W.
Alternating products of parabolic subgroups are lower Bruhat intervals: W_J1 W_J2 ... W_Jm = [e, d_m] with
d_m = w_J1 * w_J2 * ... * w_Jm (Demazure product: x * s = xs if l(xs) > l(x), else x), because [e,u] is the set of
subword products of a reduced word of u, and the subword products of any word f form [e, Dem(f)].  The block distance
m_J is monotone in Bruhat order, so the eccentricity of a J-residue is m_J(w0) = least m with d_m = w0, and the
diameter is max(m_J1(w0), m_J2(w0)).  gap = max(a)(D-1) - (N - min(a)) as in partitions.py.
Cross-check: on the 13 types of partitions.py (BFS over all of W) the diameters must agree."""
import sys, itertools
sys.path.insert(0, '.')
from weyl_dist import cartan

def setup(t, n):
    C = cartan(t, n)
    # simple reflection s_i on root coordinates: s_i(beta) = beta - <beta, alpha_i^vee> alpha_i, <beta,alpha_i^vee> = sum_j C[i][j] b_j
    def refl_matrix(i):
        M = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
        for c in range(n):          # image of alpha_c
            M[i][c] -= C[i][c]
        return M
    S = [refl_matrix(i) for i in range(n)]
    # positive roots by closure
    simple = [tuple(1 if j == i else 0 for j in range(n)) for i in range(n)]
    roots = set(simple); fr = list(simple)
    def act(M, v): return tuple(sum(M[r][c] * v[c] for c in range(n)) for r in range(n))
    while fr:
        nf = []
        for v in fr:
            for i in range(n):
                u = act(S[i], v)
                if u not in roots: roots.add(u); nf.append(u)
        fr = nf
    pos = [v for v in roots if all(x >= 0 for x in v)]
    return C, S, pos, act
def matmul(A, B):
    n = len(A); return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def analyse(t, n):
    C, S, pos, act = setup(t, n); N = len(pos)
    I = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    def length(M): return sum(1 for v in pos if any(x < 0 for x in act(M, v)) and all(x <= 0 for x in act(M, v)))
    def col(M, s): return [M[r][s] for r in range(n)]
    def longest_word(J):
        M = I; word = []
        while True:
            for s in J:
                if all(x >= 0 for x in col(M, s)):   # w(alpha_s) > 0: ws is longer
                    M = matmul(M, S[s]); word.append(s); break
            else:
                return M, word
    def demazure(M, word):
        for s in word:
            if all(x >= 0 for x in col(M, s)): M = matmul(M, S[s])
        return M
    out = []
    nodes = list(range(n))
    for k in range(1, n):
        for J1 in itertools.combinations(nodes, k):
            J2 = tuple(x for x in nodes if x not in J1)
            if J1 > J2: continue
            words = {}
            a = []
            for J in (J1, J2):
                M, w = longest_word(J); words[J] = w; a.append(len(w))
            ecc = []
            for start, other in ((J1, J2), (J2, J1)):
                M = I; m = 0
                while True:
                    m += 1; J = start if m % 2 == 1 else other
                    M = demazure(M, words[J])
                    if length(M) == N: break
                    if m > 4 * N + 4: raise RuntimeError("no convergence")
                ecc.append(m)
            D = max(ecc)
            gap = max(a) * (D - 1) - (N - min(a))
            is_colour = all(C[i][j] == 0 for J in (J1, J2) for i in J for j in J if i != j)
            out.append((gap, J1, J2, a[0], a[1], D, is_colour))
    return N, out
if __name__ == '__main__':
    types = [('A', n) for n in range(2, 9)] + [('B', n) for n in range(2, 9)] + [('D', n) for n in range(4, 9)] \
            + [('E', 6), ('E', 7), ('E', 8), ('F', 4), ('G', 2)]
    for t, n in types:
        N, res = analyse(t, n)
        tight = [(J1, J2, a1, a2, D, c) for g, J1, J2, a1, a2, D, c in res if g == 0]
        nonc = [g for g, *_, c in res if not c]
        print(f"{t}{n}: N={N}; {len(res)} partitions; gap = 0 for: "
              + (", ".join(f"{J1}|{J2} (a={a1},{a2}, D={D}{', colour classes' if c else ''})" for J1, J2, a1, a2, D, c in tight) or "none")
              + f"; smallest gap among non-colour partitions: {min(nonc) if nonc else None}", flush=True)
