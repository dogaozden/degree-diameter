"""Exact minimum of singular patterns over charts that cover both diagonals and have complete pencils, for k = 4
letters over F_q (q = 2 here).  Lemma 5: everything depends on the labelled points w_s, b_s (fixed to an orbit
representative on each side) and on per-letter star collineations sigma_s.  For each letter we list every sigma
(168 for q = 2) with its labelled U-lines U(s;t) = sigma^-1(b_s b_t) and V-lines V(s;t) = sigma(w_s w_t) (as point
masks) and its A- and B-diagonal contributions; dp_min.c then scans all combinations.
usage: python3 dp_prep.py q WNAME BNAME out.txt"""
import itertools, sys
q = int(sys.argv[1]); wn, bn, outp = sys.argv[2], sys.argv[3], sys.argv[4]; K = 4
def norm(v):
    for x in v:
        if x % q: inv = pow(x, q - 2, q); return tuple((y * inv) % q for y in v)
    return None
PTS = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)}); IDX = {p: i for i, p in enumerate(PTS)}
NP = len(PTS); FULL = (1 << NP) - 1
def span(vs):
    out = set()
    for cs in itertools.product(range(q), repeat=len(vs)):
        v = [sum(c * x[i] for c, x in zip(cs, vs)) % q for i in range(4)]
        if any(v): out.add(norm(v))
    return out
def mask(ps): return sum(1 << IDX[p] for p in ps)
e = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
if q == 2:
    REPS = {'tetra': [e[0], e[1], e[2], e[3]], 'frame': [e[0], e[1], e[2], (1, 1, 1, 0)],
            'line3': [e[0], e[1], (1, 1, 0, 0), e[2]], 'line2': [e[0], e[1], e[2], (1, 1, 0, 0)],
            'line1': [e[0], e[2], e[1], (1, 1, 0, 0)], 'line0': [e[2], e[0], e[1], (1, 1, 0, 0)]}
def rank(vs):
    rows = [list(v) for v in vs]; r = 0
    for c in range(4):
        p = next((i for i in range(r, len(rows)) if rows[i][c] % q), None)
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]; iv = pow(rows[r][c], q - 2, q); rows[r] = [(x * iv) % q for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % q: f = rows[i][c]; rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
    return r
def compl(p):
    out = []
    for c in e:
        if rank([p] + out + [c]) == 2 + len(out): out.append(c)
        if len(out) == 3: return out
PG2 = sorted({norm(v + (0,))[:3] for v in itertools.product(range(q), repeat=3) if any(v)})
MATS = []
for ent in itertools.product(range(q), repeat=9):
    M = [ent[0:3], ent[3:6], ent[6:9]]
    if rank([tuple(r) + (0,) for r in M]) == 3 and next(x for x in ent if x) == 1: MATS.append(M)
def app(M, d): return norm(tuple(sum(M[i][j] * d[j] for j in range(3)) % q for i in range(3)) + (0,))[:3]
def vec(basis, d): return tuple(sum(c * x[i] for c, x in zip(d, basis)) % q for i in range(4))
def coords(p, basis, v):
    for d in PG2:
        for a in range(q):
            w = tuple((a * p[i] + vec(basis, d)[i]) % q for i in range(4))
            if norm(w) == norm(v): return d
W = REPS[wn]; B = REPS[bn]
def edges(P):
    m = mask({norm(p) for p in P})
    for s, t in itertools.combinations(range(K), 2): m |= mask(span([P[s], P[t]]))
    return m
lines = []
with open(outp, 'w') as f:
    f.write('%d %d %d\n' % (K, edges(W), edges(B)))
    for s in range(K):
        bw, bb = compl(W[s]), compl(B[s]); others = [t for t in range(K) if t != s]
        dE = [coords(W[s], bw, W[t]) for t in others]; dEp = [coords(B[s], bb, B[t]) for t in others]
        LA = {d: mask(span([W[s], vec(bw, d)])) for d in PG2}; LB = {d: mask(span([B[s], vec(bb, d)])) for d in PG2}
        f.write('%d\n' % len(MATS))
        for M in MATS:
            inv = {app(M, d): d for d in PG2}
            U = [LA[inv[d]] for d in dEp]        # U(s;t) for t in others, labelled
            V = [LB[app(M, d)] for d in dE]      # V(s;t)
            f.write(' '.join(map(str, U + V)) + '\n')
    # b-points and w-points as masks (for pencils): b_t, w_t
    f.write(' '.join(str(mask([norm(p)])) for p in B) + '\n')
    f.write(' '.join(str(mask([norm(p)])) for p in W) + '\n')
    # planes of PG(3,q) as masks
    planes = set()
    for a, b, c in itertools.combinations(PTS, 3):
        if rank([a, b, c]) == 3: planes.add(mask(span([a, b, c])))
    f.write('%d\n%s\n' % (len(planes), ' '.join(map(str, sorted(planes)))))
print('wrote', outp, 'collineations per letter', len(MATS), 'points', NP)
