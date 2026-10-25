"""Weyl groups of root systems acting on the root lattice mod q, as subgroups of O(7,q) in standard coordinates."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ovlib as L

def cartan(edges, n):
    A = [[2 * int(i == j) for j in range(n)] for i in range(n)]
    for i, j in edges: A[i][j] = A[j][i] = -1
    return A

def reflections(A, q):
    n = len(A); mats = []
    for i in range(n):
        # s_i(c) = c - (A c)_i e_i  (root coordinates, roots of norm 2)
        S = [[int(r == c) for c in range(n)] for r in range(n)]
        for c in range(n): S[i][c] = (S[i][c] - A[i][c]) % q
        mats.append(S)
    return mats

E7 = cartan([(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 3)], 7)   # Bourbaki: 1-3-4-5-6-7, 2-4 (0-based)

if __name__ == '__main__':
    q = 11
    mats = reflections(E7, q)
    for M in mats: assert L.mat_mul(L.mat_mul(L.mat_T(M), E7, q), M, q) == [[x % q for x in r] for r in E7]
    std, P = L.conjugate_to_standard(mats, E7, q)
    G = L.std_gram(q)
    assert all(L.is_isometry(M, G, q) for M in std)
    L.write_gens(sys.argv[1], std, 'W(E7): the 7 simple reflections of the E7 root lattice mod 11, conjugated to the standard form')
    print('written', sys.argv[1])
