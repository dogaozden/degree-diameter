"""Verify the fibre model (coset-graph vertices v=(s,b,c,f), direction u=(1,0,0,9,0), infinity points (P,level))
against the point-level B-form of H(11) before using it in the annealer."""
import sys, random, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
N = len(coord)
code = coord @ (q ** np.arange(7))
assert np.all(np.diff(code) > 0), 'points not sorted by code'
def idx_of(x):
    x = np.array(x) % q
    nz = np.nonzero(x)[0][0]
    x = (x * pow(int(x[nz]), q - 2, q)) % q
    k = int(x @ (q ** np.arange(7)))
    j = int(np.searchsorted(code, k))
    assert code[j] == k, ('not a point', x)
    return j
def B(x, y):
    return int((x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % q)
# 1. infinity points: P=(x1,x2,x3,x6) with 2x1^2 + x2 x6 - x3^2 = 0, projectively normalised; lift level x4
Ps = []
for x1 in range(q):
    for x2 in range(q):
        for x3 in range(q):
            for x6 in range(q):
                if (x1, x2, x3, x6) == (0, 0, 0, 0): continue
                if (2*x1*x1 + x2*x6 - x3*x3) % q: continue
                v = (x1, x2, x3, x6)
                nz = next(t for t in v if t)
                if nz != 1: continue
                Ps.append(v)
print('P count (expect 122):', len(Ps))
# 2. fibre vertices v=(s,b,c,f); lift: offset (a,b,c,e,f) = (lam, b, c, s+9 lam, f); point (1,a,b,c,c^2-ae-bf,e,f)
def fibre_points(v):
    s, b, c, f = v
    out = []
    for lam in range(q):
        a = lam; e = (s + 9*lam) % q
        out.append(idx_of([1, a, b, c, (c*c - a*e - b*f) % q, e, f]))
    return out
def ell(P, v):
    x1, x2, x3, x6 = P; s, b, c, f = v
    return (x1*s + x2*f + x6*b - 2*x3*c) % q
def inf_point(P, level):
    x1, x2, x3, x6 = P
    return idx_of([0, x1, x2, x3, level, (2*x1) % q, x6])
random.seed(1)
bad = 0
for trial in range(300):
    v = tuple(random.randrange(q) for _ in range(4))
    P = random.choice(Ps); level = random.randrange(q)
    pts = fibre_points(v)
    ip = inf_point(P, level)
    blocked_all = [B(coord[ip], coord[j]) == 0 for j in pts]
    pred = (level + ell(P, v)) % q == 0
    if not (all(blocked_all) == pred and (any(blocked_all) == pred)):
        bad += 1
print('infinity blocking formula mismatches (of 300):', bad)
# 3. fibre-fibre: number of point-pairs (lambda, mu) with B = 0 equals 11 * R[v-w], R[d] = #roots delta of 9 delta^2 + s_d delta + (b_d f_d - c_d^2)
def R_of(d):
    s, b, c, f = d
    return sum(1 for dl in range(q) if (9*dl*dl + s*dl + (b*f - c*c)) % q == 0)
bad = 0; nonadj = 0
for trial in range(300):
    v = tuple(random.randrange(q) for _ in range(4)); w = tuple(random.randrange(q) for _ in range(4))
    pv = fibre_points(v); pw = fibre_points(w)
    conf = sum(1 for x in pv for y in pw if B(coord[x], coord[y]) == 0)
    d = tuple((a - b_) % q for a, b_ in zip(v, w))
    if conf != 11 * R_of(d): bad += 1
    if R_of(d) == 0: nonadj += 1
print('fibre conflict formula mismatches (of 300):', bad, ' compatible pairs seen:', nonadj)
# 4. D-nonsquare criterion for compatibility
sq = {(x*x) % q for x in range(1, q)}
def D(d):
    s, b, c, f = d
    return (s*s + 3*c*c + 8*b*f) % q
bad = 0
for trial in range(2000):
    d = tuple(random.randrange(q) for _ in range(4))
    if d == (0,0,0,0): continue
    adj = R_of(d) == 0
    pred = (D(d) not in sq) and D(d) != 0
    if adj != pred: bad += 1
print('compatibility <-> D nonsquare mismatches (of 2000):', bad)
