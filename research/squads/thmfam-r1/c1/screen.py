#!/usr/bin/env python3
"""Screen all integer lift pairs (X, Y), entries in [-3,3], det 1, family S = O(X) u O(Y), PSL(2,q).
Symmetry reduction: (1) O(M) depends only on the class of M under M -> +-w^k M w^-k (k = 0,1,2) and sign;
(2) unordered pairs of classes; (3) conjugation by r in GL(2,Z) with r w r^-1 in {w, w^-1} (an automorphism of PSL(2,q)).
Pairs whose 6 elements are not distinct in PSL(2,p) for some prime p in [23,113] are dropped.
Screen: haar_ecc psl on --qs (default 29,41,53); excess = diam - log_5 |PSL| (Delta-1 = 5), mean over the screen primes.
Output: screen.tsv (one line per surviving pair, sorted by mean excess)."""
import itertools, math, re, subprocess, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
HAAR = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
SCREEN_QS = [29, 41, 53]
PRIMES = [q for q in range(23, 114) if all(q % d for d in range(2, int(q**.5)+1))]
def mul(A, B):
    a,b,c,d = A; e,g,h,i = B
    return (a*e+b*h, a*g+b*i, c*e+d*h, c*g+d*i)
w = (0,-1,1,-1); wi = (-1,1,-1,0)
def norm(M):
    lead = next(t for t in M if t)
    return M if lead > 0 else tuple(-t for t in M)
def conj_by(r, rinv, M): return mul(mul(r, M), rinv)
def orbit(M): return [M, conj_by(w, wi, M), conj_by(wi, w, M)]   # w^2 M w^-2 = w^-1 M w
def cls_key(M): return frozenset(norm(X) for X in orbit(M))
# box
box = [(a,b,c,d) for a,b,c,d in itertools.product(range(-3,4), repeat=4) if a*d-b*c == 1]
classes = {}   # key -> (height, representative)
for M in box:
    k = cls_key(M); h = max(abs(t) for t in M)
    if k not in classes or h < classes[k][0]: classes[k] = (h, M)
# normalizer of <w> in GL(2,Z): small entries
R = []
for r in itertools.product(range(-2,3), repeat=4):
    det = r[0]*r[3]-r[1]*r[2]
    if det not in (1,-1): continue
    adj = (r[3], -r[1], -r[2], r[0]); rinv = tuple(t*det for t in adj)   # inverse of r in GL(2,Z)
    rw = conj_by(r, rinv, w)
    if rw in (w, wi): R.append((r, rinv))
R = [(r, ri) for r, ri in R]
def transform(key, r, ri):
    return frozenset(norm(conj_by(r, ri, M)) for M in key)
def pair_canon(k1, k2):
    best = None
    for (r, ri) in [((1,0,0,1),(1,0,0,1))] + R:
        t1, t2 = transform(k1, r, ri), transform(k2, r, ri)
        pair = tuple(sorted([tuple(sorted(t1)), tuple(sorted(t2))]))
        if best is None or pair < best: best = pair
    return best
def pkey(M, q):
    M = tuple(t % q for t in M); lead = next(t for t in M if t)
    return M if lead <= (q-1)//2 else tuple((-t) % q for t in M)
def distinct_all(X, Y):
    S = orbit(X) + orbit(Y)
    for q in PRIMES:
        if len({pkey(M, q) for M in S}) != 6: return False
    return True
keys = list(classes.keys())
print(f"box det-1 matrices: {len(box)}, classes: {len(keys)}, normalizer elements: {len(R)}", file=sys.stderr)
seen = set(); pairs = []
for k1, k2 in itertools.combinations(keys, 2):
    c = pair_canon(k1, k2)
    if c in seen: continue
    seen.add(c)
    h1, X = classes[k1]; h2, Y = classes[k2]
    if not distinct_all(X, Y): continue
    pairs.append((max(h1, h2), X, Y))
print(f"canonical pairs surviving distinctness: {len(pairs)}", file=sys.stderr)
RE = re.compile(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)')
def score_one(X, Y, q):
    S = orbit(X) + orbit(Y)
    inp = ''.join(f"{' '.join(str(t % q) for t in M)} 0\n" for M in S)
    out = subprocess.run([HAAR, 'psl', str(q), '1'], input=inp, capture_output=True, text=True, timeout=600).stdout
    m = RE.search(out)
    if not m: return None
    d, eA, eB, cA, cB, order, conn, diam = m.groups()
    if conn != 'yes' or cA != cB: return None
    G = int(cA) // 2
    return max(int(eA), int(eB)) - math.log(G) / math.log(int(d) - 1)
qs = SCREEN_QS
if len(sys.argv) > 1: qs = [int(x) for x in sys.argv[1].split(',')]
rows = []
for i, (h, X, Y) in enumerate(pairs):
    ex = [score_one(X, Y, q) for q in qs]
    if any(e is None for e in ex): continue
    rows.append((sum(ex)/len(ex), h, X, Y, ex))
rows.sort()
with open(os.path.join(HERE, 'screen.tsv'), 'w') as f:
    f.write('mean_excess\theight\tX\tY\texcess_per_q(' + ','.join(map(str, qs)) + ')\n')
    for mean, h, X, Y, ex in rows:
        f.write(f"{mean:.3f}\t{h}\t{' '.join(map(str,X))}\t{' '.join(map(str,Y))}\t{' '.join(f'{e:.3f}' for e in ex)}\n")
print(f"screened {len(rows)} pairs on q={qs}", file=sys.stderr)
for r in rows[:15]: print(f"{r[0]:.3f} h={r[1]} X={r[2]} Y={r[3]} ex={[round(e,3) for e in r[4]]}")
