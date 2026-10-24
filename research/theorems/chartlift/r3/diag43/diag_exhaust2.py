"""Exhaustive test: can a 4-letter chart over F_3^4 cover BOTH diagonals (closed backtracking 4-walks reach the whole
fibre on side A and on side B)?

Reduction.  Changing coordinates independently in the A-fibres and the B-fibres (A_s -> Q A_s P^-1, b_s -> Q b_s) gives
an isomorphic lift, so the points w_s = A_s^-1 b_s (A-space) and b_s (B-space) can be fixed to one representative of
each PGL(4,3)-orbit of labelled 4-tuples of points.  The A-diagonal is the union of the points w_s, the lines w_s w_t
and the lines U(s;t) = A_s^-1 <b_s, b_t> (through w_s); the B-diagonal is the union of b_s, b_s b_t and
V(s;t) = A_s <w_s, w_t> (through b_s).  A_s enters only through the collineation sigma_s it induces from the star of
lines at w_s to the star at b_s: U(s;t) = sigma_s^-1(b_s b_t) and V(s;t) = sigma_s(w_s w_t).  Every collineation
(an element of PGL(3,3), 5,616 of them) is induced by some A_s.  So for each pair of orbit representatives we
enumerate, per letter s, the 5,616 maps sigma_s, record which points of PG(3,3) the U-lines at w_s and the V-lines
at b_s cover, and search for 4 choices whose unions cover all 40 points on both sides.
usage: python3 diag_exhaust.py [q]   (q = 3 default; q = 2 runs the same test for 3 letters... see K below)"""
import itertools, sys
q = 3; K = 4
def norm(v):
    for x in v:
        if x: inv = pow(x, q - 2, q); return tuple((y * inv) % q for y in v)
    return None
PTS = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
IDX = {p: i for i, p in enumerate(PTS)}; NP = len(PTS)
def span_pts(vs):
    out = set()
    for cs in itertools.product(range(q), repeat=len(vs)):
        v = [sum(c * x[i] for c, x in zip(cs, vs)) % q for i in range(4)]
        if any(v): out.add(norm(v))
    return out
def mask(points): return sum(1 << IDX[p] for p in points)
def line_mask(a, b): return mask(span_pts([a, b]))
FULL = (1 << NP) - 1
# orbit representatives of labelled 4-tuples of points (w_0..w_3) up to PGL(4,3)
e = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
REPS = {
    'tetra': [e[0], e[1], e[2], e[3]],
    'quad': [e[0], e[1], e[2], (1, 1, 1, 0)],
    'col3_off3': [e[0], e[1], (1, 1, 0, 0), e[2]],     # w0, w1, w2 collinear, w3 off
    'col3_off2': [e[0], e[1], e[2], (1, 1, 0, 0)],
    'col3_off1': [e[0], e[2], e[1], (1, 1, 0, 0)],
    'col3_off0': [e[2], e[0], e[1], (1, 1, 0, 0)],
    'col4': [e[0], e[1], (1, 1, 0, 0), (1, 2, 0, 0)],
}
# coincidences (w_s = w_t) are handled separately below
def complement_basis(p):
    """3 vectors completing p to a basis: star(p) = PG(F^4/<p>) with coordinates in this basis."""
    for cand in itertools.combinations(e + [(1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1), (1, 0, 1, 0)], 3):
        M = [list(p)] + [list(c) for c in cand]
        if det4(M) % q: return [tuple(c) for c in cand]
def det4(M):
    import itertools as it
    s = 0
    for perm in it.permutations(range(4)):
        sgn = 1
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]: sgn = -sgn
        t = sgn
        for i in range(4): t *= M[i][perm[i]]
        s += t
    return s
def star_coords(p, basis, v):
    """coordinates of the line <p, v> in star(p): solve v = a p + sum c_i basis_i, return normalized (c_1, c_2, c_3)."""
    for a in range(q):
        for cs in itertools.product(range(q), repeat=3):
            w = [(a * p[i] + sum(c * b[i] for c, b in zip(cs, basis))) % q for i in range(4)]
            if norm(w) == norm(v) and any(cs): return norm(list(cs))
    raise ValueError
PG2 = sorted({norm(v) for v in itertools.product(range(q), repeat=3) if any(v)})
def pgl3():
    mats = []
    for entries in itertools.product(range(q), repeat=9):
        M = [entries[0:3], entries[3:6], entries[6:9]]
        d = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
             + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])) % q
        if d == 0: continue
        first = next(x for x in entries if x)
        if first != 1: continue          # one representative per scalar class
        mats.append(M)
    return mats
MATS = pgl3()
def apply(M, v): return norm([sum(M[i][j] * v[j] for j in range(3)) % q for i in range(3)])
PERMS = [tuple(apply(M, v) for v in PG2) for M in MATS]   # sigma as a permutation of PG2 (index order)
P2I = {v: i for i, v in enumerate(PG2)}
def per_letter(W, B, s):
    """distinct (A-cover mask, B-cover mask) over all sigma: star(w_s) -> star(b_s)."""
    bw, bb = complement_basis(W[s]), complement_basis(B[s])
    # star(w_s) direction (PG2 point) -> line mask through w_s; same at b_s
    lineA = {}; lineB = {}
    for d in PG2:
        v = [sum(c * x[i] for c, x in zip(d, bw)) % q for i in range(4)]; lineA[d] = line_mask(W[s], v)
        v = [sum(c * x[i] for c, x in zip(d, bb)) % q for i in range(4)]; lineB[d] = line_mask(B[s], v)
    others = [t for t in range(K) if t != s]
    dirE = [star_coords(W[s], bw, W[t]) if norm(W[t]) != norm(W[s]) else None for t in others]   # w_s w_t in star(w_s)
    dirEp = [star_coords(B[s], bb, B[t]) if norm(B[t]) != norm(B[s]) else None for t in others]  # b_s b_t in star(b_s)
    out = set()
    for perm in PERMS:
        inv = {perm[i]: PG2[i] for i in range(len(PG2))}
        mA = 0; mB = 0
        for d in dirEp:                      # U(s;t) = sigma^-1(b_s b_t)
            if d is not None: mA |= lineA[inv[d]]
        for d in dirE:                       # V(s;t) = sigma(w_s w_t)
            if d is not None: mB |= lineB[perm[P2I[d]]]
        out.add((mA, mB))
    return out
def edges_mask(W):
    m = mask({norm(w) for w in W})
    for s, t in itertools.combinations(range(K), 2):
        if norm(W[s]) != norm(W[t]): m |= line_mask(W[s], W[t])
    return m
def search(W, B):
    need = (FULL & ~edges_mask(W), FULL & ~edges_mask(B))
    cands = [sorted(per_letter(W, B, s)) for s in range(K)]
    # keep only maximal pairs per letter (dominance pruning)
    pruned = []
    for c in cands:
        c = sorted(set((a & need[0], b & need[1]) for a, b in c), key=lambda x: -(bin(x[0]).count('1') + bin(x[1]).count('1')))
        keep = []
        for a, b in c:
            if not any((a | a2) == a2 and (b | b2) == b2 for a2, b2 in keep): keep.append((a, b))
        pruned.append(keep)
    sizes = [len(c) for c in pruned]
    import subprocess
    inp = '%d %d\n' % need
    for c in pruned:
        inp += '%d\n' % len(c) + ''.join('%d %d\n' % (a, b) for a, b in c)
    cap = 3 * q          # 3 lines through the apex, q further points each
    out = subprocess.run(['./diag_dfs', str(cap)], input=inp, capture_output=True, text=True).stdout.strip()
    return sizes, out
if __name__ == '__main__':
    names = list(REPS)
    anyfound = False
    for wn in names:
        for bn in names:
            sizes, out = search(REPS[wn], REPS[bn])
            ok = out.startswith('FOUND')
            print('w=%-10s b=%-10s per-letter maximal pairs %s: %s (%s)' % (wn, bn, sizes, 'BOTH DIAGONALS COVERABLE' if ok else 'impossible', out), flush=True)
            anyfound |= ok
    print('RESULT:', 'some configuration covers both diagonals' if anyfound else 'no chart covers both diagonals (non-coincident w, b)')
