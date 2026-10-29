"""Task (1): e4 + one affine line t + GF(p) u with Qp(u) non-square: pairwise opposite (direct B on 7 coords),
the q+1 points lie in a plane, and form a conic (no three collinear, unique conic through them, nonsingular)."""
import sys, itertools, random
from hexaffine import point7, B7, Q7, qp, rank_mod, nullspace_mod, is_square, nonsquare_direction

def run(p):
    u = nonsquare_direction(p)
    t = (0, 0, 0, 0, 0)  # a line through the origin of the chart; also test a random t below
    out = {}
    e4 = [0, 0, 0, 0, 1, 0, 0]
    assert Q7(e4, p) == 0
    # B(x,x') = Qp(x - x') sanity on random pairs (fibration formula)
    rng = random.Random(1)
    for _ in range(2000):
        v = [rng.randrange(p) for _ in range(5)]
        w = [rng.randrange(p) for _ in range(5)]
        x, y = point7(v, p), point7(w, p)
        d = [(v[i] - w[i]) % p for i in range(5)]
        assert B7(x, y, p) == qp(d, p), "fibration formula mismatch"
    out['B_equals_Qp_on_2000_random_pairs'] = True
    out['Qp(u)'] = qp(u, p)
    out['Qp(u)_nonsquare'] = not is_square(qp(u, p), p)
    for tt in [t, tuple(rng.randrange(p) for _ in range(5))]:
        pts = [e4] + [point7([(tt[i] + lam * u[i]) % p for i in range(5)], p).tolist() for lam in range(p)]
        pts = [list(map(int, x)) for x in pts]
        # points on the quadric Q(6,p) (= H(p) point set)
        assert all(Q7(x, p) == 0 for x in pts)
        # pairwise opposite: B != 0 for all distinct pairs (direct 7-coordinate B)
        bad = [(i, j) for i, j in itertools.combinations(range(len(pts)), 2) if B7(pts[i], pts[j], p) == 0]
        ok_opp = not bad
        # plane: rank of the q+1 vectors is 3
        rk = rank_mod(pts, p)
        # conic: coordinates in a basis of the span
        # pick 3 independent points as basis
        basis_idx = []
        for i in range(len(pts)):
            if rank_mod([pts[j] for j in basis_idx + [i]], p) == len(basis_idx) + 1:
                basis_idx.append(i)
            if len(basis_idx) == 3:
                break
        Bm = [pts[i] for i in basis_idx]
        # solve coordinates: x = sum c_k Bm[k]; brute force over p^3 is fine for p<=7
        coords = []
        table = {}
        for c0 in range(p):
            for c1 in range(p):
                for c2 in range(p):
                    v = tuple((c0 * Bm[0][j] + c1 * Bm[1][j] + c2 * Bm[2][j]) % p for j in range(7))
                    table[v] = (c0, c1, c2)
        for x in pts:
            coords.append(table[tuple(x)])
        # no three collinear: 3x3 determinants nonzero
        def det3(a, b, c):
            return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0])) % p
        collinear = [(i, j, k) for i, j, k in itertools.combinations(range(len(coords)), 3)
                     if det3(coords[i], coords[j], coords[k]) == 0]
        # conic through all q+1 points: monomials x^2,y^2,z^2,xy,xz,yz
        mons = lambda c: [c[0]*c[0], c[1]*c[1], c[2]*c[2], c[0]*c[1], c[0]*c[2], c[1]*c[2]]
        ns = nullspace_mod([mons(c) for c in coords], p)
        conic_info = None
        if len(ns) == 1:
            m = ns[0]
            S = [[m[0], m[3] * pow(2, p - 2, p) % p, m[4] * pow(2, p - 2, p) % p],
                 [m[3] * pow(2, p - 2, p) % p, m[1], m[5] * pow(2, p - 2, p) % p],
                 [m[4] * pow(2, p - 2, p) % p, m[5] * pow(2, p - 2, p) % p, m[2]]]
            d = (S[0][0]*(S[1][1]*S[2][2]-S[1][2]*S[2][1]) - S[0][1]*(S[1][0]*S[2][2]-S[1][2]*S[2][0])
                 + S[0][2]*(S[1][0]*S[2][1]-S[1][1]*S[2][0])) % p
            conic_info = {'nullity': len(ns), 'conic_det_nonzero': d != 0}
        else:
            conic_info = {'nullity': len(ns)}
        key = 'tt=' + ''.join(map(str, tt))
        out[key] = {'n_points': len(pts), 'pairwise_opposite': ok_opp, 'bad_pairs': bad[:3],
                    'rank_of_span': rk, 'in_plane': rk == 3, 'collinear_triples': len(collinear),
                    'conic': conic_info, 'u': list(u)}
        print(p, key, out[key], flush=True)
    return out

if __name__ == '__main__':
    for p in map(int, sys.argv[1:] or ['5', '7']):
        run(p)
