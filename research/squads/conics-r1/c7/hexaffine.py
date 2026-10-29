"""Card c7 helpers: points of H(p) opposite e4 in the chart x0 = 1, B computed directly on 7 coordinates.

Points of H(p) = points of Q(6,p): Q(x) = x0x4 + x1x5 + x2x6 - x3^2, B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3.
Opposite e4 (B(x,e4) = x0 != 0): x = (1, a, b, c, c^2 - a e - b f, e, f).
Affine quadratic form Qp(a,b,c,e,f) = c^2 - a e - b f (from B(x,x') = Qp(x - x'), checked in verify_line.py)."""
import numpy as np

def is_square(n, p):
    n %= p
    return n != 0 and any((k * k - n) % p == 0 for k in range(1, p))

def qp(v, p):
    a, b, c, e, f = [int(t) for t in v]
    return (c * c - a * e - b * f) % p

def point7(v, p):
    a, b, c, e, f = [int(t) for t in v]
    return np.array([1, a, b, c, (c * c - a * e - b * f) % p, e, f], dtype=np.int64) % p

def B7(x, y, p):
    return int((x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % p)

def Q7(x, p):
    return int((x[0]*x[4] + x[1]*x[5] + x[2]*x[6] - x[3]*x[3]) % p)

def rank_mod(M, p):
    M = [list(map(lambda t: int(t) % p, row)) for row in M]
    r = 0
    ncols = len(M[0]) if M else 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][c] % p), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(t * inv) % p for t in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(ncols)]
        r += 1
    return r

def nullspace_mod(M, p):
    """Basis of the right null space of M (list of rows) over GF(p)."""
    M = [list(map(lambda t: int(t) % p, row)) for row in M]
    ncols = len(M[0])
    r = 0
    pivcols = []
    for c in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][c] % p), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(t * inv) % p for t in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(ncols)]
        pivcols.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in pivcols]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for i, pc in enumerate(pivcols):
            v[pc] = (-M[i][fc]) % p
        basis.append(v)
    return basis

def nonsquare_direction(p):
    """u = (1,0,1,e,0) with Qp(u) = 1 - e a non-square (smallest such e)."""
    for e in range(p):
        n = (1 - e) % p
        if n != 0 and not is_square(n, p):
            return (1, 0, 1, e, 0)
    raise ValueError
