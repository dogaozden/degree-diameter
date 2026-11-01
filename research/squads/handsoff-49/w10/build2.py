"""Second batch of w10 group tables: extra centreless groups with small abelianization (see NOTES.md)."""
import sys, numpy as np
import mk
from groups import table as gtable
from build1 import companion, ident, mpow, OUT

def gf16_mult_matrices():
    """4x4 GF(2) matrices: alpha (root of x^4+x+1) and alpha^3 (order 5), and the Frobenius x -> x^4."""
    def mul_poly(a, b):  # ints as GF(2)[x] polynomials, reduce mod x^4+x+1
        r = 0
        for i in range(4):
            if (b >> i) & 1:
                r ^= a << i
        for i in range(7, 3, -1):
            if (r >> i) & 1:
                r ^= 0b10011 << (i - 4)
        return r
    def to_mat(f):  # matrix of multiplication by f on basis 1, x, x^2, x^3 (columns = images)
        cols = [mul_poly(f, 1 << i) for i in range(4)]
        return tuple(tuple((cols[j] >> i) & 1 for j in range(4)) for i in range(4))
    def power(a, k):
        r = 1
        for _ in range(k):
            r = mul_poly(r, a)
        return r
    alpha = 0b10
    zeta = power(alpha, 3)
    frob = to_mat(1)  # placeholder; build the Frobenius as a map on basis vectors
    cols = [power(power(alpha, i), 4) for i in range(4)]  # (alpha^i)^4 as ints
    F = tuple(tuple((cols[j] >> i) & 1 for j in range(4)) for i in range(4))
    return to_mat(alpha), to_mat(zeta), F

def block2(A, B):
    n, m = len(A), len(B)
    M = [[0] * (n + m) for _ in range(n + m)]
    for i in range(n):
        for j in range(n):
            M[i][j] = A[i][j]
    for i in range(m):
        for j in range(m):
            M[n + i][n + j] = B[i][j]
    return tuple(tuple(r) for r in M)

def diag2(A):
    return block2(A, A)

def z5_frob_gens():
    _, Z, F = gf16_mult_matrices()
    Z8 = diag2(Z)  # zeta acting on F16^2 = F2^8
    U = [[0] * 8 for _ in range(8)]
    for i in range(8):
        U[i][i] = 1
    for i in range(4):
        U[i][4 + i] = 1  # [[I, I],[0, I]]
    U = tuple(tuple(r) for r in U)
    zu = mk.mat_mul(Z8, U, 2)
    sigma = diag2(F)
    return zu, Z8, sigma

def gl23_gens():
    return [((1, 1, 0), (0, 1, 0), (0, 0, 1)), ((0, 1, 0), (1, 0, 0), (0, 0, 1)),
            ((2, 0, 0), (0, 1, 0), (0, 0, 1)), ((1, 0, 0), (0, 1, 0), (0, 0, 2))]

def irred_quadratic_order(p, want):
    for c0 in range(1, p):
        for c1 in range(p):
            M = companion([c0, c1], p)
            if mpow(M, want, p) == ident(2) and mpow(M, want // 2, p) != ident(2):
                if all((x * x + c1 * x + c0) % p for x in range(p)):
                    return M
    raise RuntimeError

SPECS = {
    "Z3p3_GL23xZ2": lambda: mk.semidirect_vec(3, 3, gl23_gens()),
    "Z2p8_Z10": lambda: mk.semidirect_vec(2, 8, [z5_frob_gens()[0]]),
    "Z2p8_D5": lambda: mk.semidirect_vec(2, 8, [z5_frob_gens()[1], z5_frob_gens()[2]]),
    "Z19sq_Z8": lambda: mk.semidirect_vec(19, 2, [irred_quadratic_order(19, 8)]),
    "Z19sq_D4": lambda: mk.semidirect_vec(19, 2, [((0, 18), (1, 0)), ((1, 0), (0, 18))]),
    "Z11sq_D11": lambda: mk.semidirect_vec(11, 2, [((1, 1), (0, 1)), ((10, 0), (0, 1))]),
    "S4xAGL11": lambda: gtable("perm 4 1,0,2,3 ; 1,2,3,0 x agl1 11"),
    "Z37sq_Z2": lambda: mk.semidirect_vec(37, 2, [((36, 0), (0, 36))]),
}

if __name__ == "__main__":
    which = sys.argv[1:] or list(SPECS)
    for name in which:
        T = SPECS[name]()
        pr = mk.props(T, name)
        mk.write_bin(T, OUT + name + ".bin")
        print(pr, flush=True)
