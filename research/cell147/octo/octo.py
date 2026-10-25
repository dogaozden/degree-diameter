"""Octonions on the E7 frame: basis 1, u0..u6 (u_i = frame root f_i, norm 1 for B' = B/2), Fano lines from e7frame.py.
mult(orient) builds the 8x8x8 structure constants for one orientation choice of the 7 lines."""
import itertools, numpy as np
LINES = [(0, 1, 3), (0, 2, 4), (0, 5, 6), (1, 2, 5), (1, 4, 6), (2, 3, 6), (3, 4, 5)]
def mult(orient):
    T = np.zeros((8, 8, 8), dtype=np.int64)         # e_i e_j = sum_k T[i,j,k] e_k ; index 0 = 1, index a+1 = u_a
    for i in range(8):
        T[0, i, i] = 1; T[i, 0, i] = 1
    for a in range(7): T[a + 1, a + 1, 0] = -1
    for (a, b, c), o in zip(LINES, orient):
        if o < 0: a, b = b, a
        for x, y, z in ((a, b, c), (b, c, a), (c, a, b)):
            T[x + 1, y + 1, z + 1] = 1; T[y + 1, x + 1, z + 1] = -1
    return T
def prod(T, x, y): return np.einsum('i,j,ijk->k', x, y, T)
def is_alternative(T):
    E = np.eye(8, dtype=np.int64)
    for i in range(8):
        for j in range(8):
            x, y = E[i], E[j]
            if not np.array_equal(prod(T, prod(T, x, x), y), prod(T, x, prod(T, x, y))): return False
            if not np.array_equal(prod(T, prod(T, y, x), x), prod(T, y, prod(T, x, x))): return False
    # also for sums of two basis elements (alternativity is quadratic)
    for i, j, k in itertools.combinations(range(1, 8), 3):
        x = E[i] + E[j]; y = E[k]
        if not np.array_equal(prod(T, prod(T, x, x), y), prod(T, x, prod(T, x, y))): return False
    return True
if __name__ == "__main__":
    good = [o for o in itertools.product((1, -1), repeat=7) if is_alternative(mult(o))]
    print('alternative orientations:', len(good)); print(good[:4])
