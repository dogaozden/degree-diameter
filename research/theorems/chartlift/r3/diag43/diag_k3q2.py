"""Can a 3-letter chart over F_2^4 cover both diagonals?  Same reduction as diag_exhaust.py (points fixed up to
PGL(4,2) on each side, collineations sigma_s: star(w_s) -> star(b_s) in PGL(3,2), 168 each); brute force over all
triples of per-letter (A-mask, B-mask) pairs.  Configurations of 3 labelled points: independent ('tri'), collinear
('col', the 3 points of a line), and coincidences.  For each covering triple we build the chart and report singular
patterns and pencils (chart_eval)."""
import itertools, subprocess, sys
q = 2; K = 3
def norm(v):
    return tuple(v) if any(v) else None
PTS = sorted({tuple(v) for v in itertools.product(range(2), repeat=4) if any(v)}); IDX = {p: i for i, p in enumerate(PTS)}
FULL = (1 << len(PTS)) - 1
def span(vs):
    out = set()
    for cs in itertools.product(range(2), repeat=len(vs)):
        v = tuple(sum(c * x[i] for c, x in zip(cs, vs)) % 2 for i in range(4))
        if any(v): out.add(v)
    return out
def mask(ps): return sum(1 << IDX[p] for p in ps)
e = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
REPS = {'tri': [e[0], e[1], e[2]], 'col': [e[0], e[1], (1, 1, 0, 0)],
        'co01': [e[0], e[0], e[1]], 'co02': [e[0], e[1], e[0]], 'co12': [e[1], e[0], e[0]], 'co012': [e[0], e[0], e[0]]}
def rank(vs):
    rows = [list(v) for v in vs]; r = 0
    for c in range(4):
        p = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c]: rows[i] = [(a + b) % 2 for a, b in zip(rows[i], rows[r])]
        r += 1
    return r
def compl(p):
    out = []
    for c in e:
        if rank([p] + out + [c]) == 2 + len(out): out.append(c)
        if len(out) == 3: return out
PG2 = [v for v in itertools.product(range(2), repeat=3) if any(v)]
MATS = []
for ent in itertools.product(range(2), repeat=9):
    M = [ent[0:3], ent[3:6], ent[6:9]]
    if rank([tuple(r) + (0,) for r in M]) == 3: MATS.append(M)
assert len(MATS) == 168
def app(M, d): return tuple(sum(M[i][j] * d[j] for j in range(3)) % 2 for i in range(3))
def vec(p, basis, d): return tuple(sum(c * x[i] for c, x in zip(d, basis)) % 2 for i in range(4))
def coords(p, basis, v):
    for d in PG2:
        for a in range(2):
            if tuple((a * p[i] + vec(p, basis, d)[i]) % 2 for i in range(4)) == tuple(v): return d
    return None
def per_letter(W, B, s):
    bw, bb = compl(W[s]), compl(B[s]); others = [t for t in range(K) if t != s]
    dE = [coords(W[s], bw, W[t]) if W[t] != W[s] else None for t in others]
    dEp = [coords(B[s], bb, B[t]) if B[t] != B[s] else None for t in others]
    lineA = {d: mask(span([W[s], vec(W[s], bw, d)])) for d in PG2}; lineB = {d: mask(span([B[s], vec(B[s], bb, d)])) for d in PG2}
    out = {}
    for M in MATS:
        inv = {app(M, d): d for d in PG2}
        mA = 0; mB = 0
        for d in dEp:
            if d is not None: mA |= lineA[inv[d]]
        for d in dE:
            if d is not None: mB |= lineB[app(M, d)]
        out.setdefault((mA, mB), []).append(M)
    return out, bw, bb
def edges(W):
    m = mask(set(W))
    for s, t in itertools.combinations(range(K), 2):
        if W[s] != W[t]: m |= mask(span([W[s], W[t]]))
    return m
def lift(W, B, s, M, bw, bb):
    # A_s w_s = b_s, A_s bw_i = sum_j M[j][i] bb_j ; solve A_s = D S^-1 over F_2 by brute force on the inverse
    S = [[([W[s]] + bw)[c][r] for c in range(4)] for r in range(4)]
    dst = [B[s]] + [vec(B[s], bb, tuple(M[j][i] for j in range(3))) for i in range(3)]
    D = [[dst[c][r] for c in range(4)] for r in range(4)]
    # invert S
    T = [S[r][:] + [int(r == c) for c in range(4)] for r in range(4)]
    for c in range(4):
        p = next(r for r in range(c, 4) if T[r][c]); T[c], T[p] = T[p], T[c]
        for r in range(4):
            if r != c and T[r][c]: T[r] = [(a + b) % 2 for a, b in zip(T[r], T[c])]
    Si = [row[4:] for row in T]
    return [[sum(D[i][t] * Si[t][j] for t in range(4)) % 2 for j in range(4)] for i in range(4)]
total = 0
for wn, W in REPS.items():
    for bn, B in REPS.items():
        need = (FULL & ~edges(W), FULL & ~edges(B))
        L = [per_letter(W, B, s) for s in range(K)]
        found = []
        for (p0, l0), (p1, l1), (p2, l2) in itertools.product(L[0][0].items(), L[1][0].items(), L[2][0].items()):
            if (need[0] & ~(p0[0] | p1[0] | p2[0])) == 0 and (need[1] & ~(p0[1] | p1[1] | p2[1])) == 0:
                found.append((l0[0], l1[0], l2[0]))
        total += len(found)
        line = 'w=%-5s b=%-5s covering mask triples: %d' % (wn, bn, len(found))
        if found:
            txt = ''
            for Ms in found:
                As = [lift(W, B, s, Ms[s], L[s][1], L[s][2]) for s in range(K)]
                txt += ''.join(' '.join(str(x) for row in A for x in row) + '\n' for A in As) + ''.join(' '.join(map(str, B[s])) + '\n' for s in range(K))
            res = subprocess.run(['./chart_eval', '../../tables/gf2.txt', '3'], input=txt, capture_output=True, text=True).stdout.split('\n')
            stats = sorted({tuple(map(int, r.split())) for r in res if r.strip()})
            line += '; (singular, pencil-miss vectors, diag-miss vectors) seen: %s' % stats[:12]
        print(line, flush=True)
print('total covering triples', total)
