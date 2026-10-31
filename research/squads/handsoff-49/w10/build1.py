"""Build the first batch of w10 group tables (card list) and report their facts."""
import sys, itertools, numpy as np
import mk
from groups import table as gtable

OUT = "/home/user/degree-diameter/research/squads/handsoff-49/w10/tabs/"

def companion(coeffs, p):
    """Companion matrix of monic x^d + c_{d-1} x^{d-1} + ... + c_0 (coeffs = [c0..c_{d-1}])."""
    d = len(coeffs)
    M = [[0] * d for _ in range(d)]
    for i in range(1, d):
        M[i][i - 1] = 1
    for i in range(d):
        M[i][d - 1] = (-coeffs[i]) % p
    return tuple(tuple(r) for r in M)

def ident(d):
    return tuple(tuple(1 if i == j else 0 for j in range(d)) for i in range(d))

def mpow(M, k, p):
    R = ident(len(M))
    for _ in range(k):
        R = mk.mat_mul(R, M, p)
    return R

def gf17_order9():
    p = 17
    for c0 in range(1, p):
        for c1 in range(p):
            M = companion([c0, c1], p)
            if mpow(M, 9, p) == ident(2) and mpow(M, 3, p) != ident(2):
                if all((x * x + c1 * x + c0) % p for x in range(p)):
                    return M
    raise RuntimeError

def gf3_order11_quintic():
    p = 3
    for cs in itertools.product(range(p), repeat=5):
        if cs[0] == 0:
            continue
        M = companion(list(cs), p)
        if mpow(M, 11, p) == ident(5) and M != ident(5):
            return M
    raise RuntimeError

def sl2_3_in_sl2_11():
    p = 11
    rng = np.random.default_rng(3)
    def rand_sl2():
        while True:
            a, b, c = (int(v) for v in rng.integers(0, p, 3))
            if a == 0:
                continue
            d = ((1 + b * c) * pow(a, p - 2, p)) % p
            return ((a, b), (c, d))
    for _ in range(20000):
        x, y = rand_sl2(), rand_sl2()
        els, _ = mk.mat_closure([x, y], p)
        if len(els) != 24:
            continue
        orders = {}
        for g in els:
            o = 1; h = g
            while h != ident(2):
                h = mk.mat_mul(h, g, p); o += 1
            orders[o] = orders.get(o, 0) + 1
        if orders == {1: 1, 2: 1, 3: 8, 4: 6, 6: 8}:
            return [x, y]
    raise RuntimeError

def qmat_j(p):
    for a in range(p):
        for b in range(p):
            if (a * a + b * b + 1) % p == 0:
                return ((a, b), (b, (-a) % p))
    raise RuntimeError

SPECS = {
    "A5xAGL17": lambda: gtable("perm 5 1,2,0,3,4 ; 1,2,3,4,0 x agl1 7"),
    "S5x_Z7Z3": lambda: gtable("perm 5 1,0,2,3,4 ; 1,2,3,4,0 x meta 7 3 2"),
    "Z17sq_Z9": lambda: mk.semidirect_vec(17, 2, [gf17_order9()]),
    "Z29sq_Z3": lambda: mk.semidirect_vec(29, 2, [((0, 28), (1, 28))]),
    "Z3p5_Z11": lambda: mk.semidirect_vec(3, 5, [gf3_order11_quintic()]),
    "Z19sq_Q8": lambda: mk.semidirect_vec(19, 2, [((0, 18), (1, 0)), qmat_j(19)]),
    "Z11sq_SL23": lambda: mk.semidirect_vec(11, 2, sl2_3_in_sl2_11()),
    "ASL25": lambda: mk.semidirect_vec(5, 2, [((1, 1), (0, 1)), ((0, 4), (1, 0))]),
    "F7Z3xF13Z12": lambda: gtable("meta 7 3 2 x meta 13 12 2"),
}

if __name__ == "__main__":
    which = sys.argv[1:] or list(SPECS)
    for name in which:
        T = SPECS[name]()
        pr = mk.props(T, name)
        mk.write_bin(T, OUT + name + ".bin")
        print(pr, flush=True)
