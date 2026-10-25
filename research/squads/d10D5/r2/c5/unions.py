#!/usr/bin/env python3
"""unions.py GQBIN SEED NELEM M OUTDIR [NPAIRS]: card c5 round 2.
Semiregular order-M collineations of W(7) (points cycles all M): powers of random PGSp elements.  Their flag orbits
(size M, distinct points and lines); single orbits with exact matching (Matcher.size == N; necessary for any union,
since adding flags only tightens the matching); then random disjoint pairs of feasible orbits: exact matching size,
and the number of collinear freed-point pairs (cp) and concurrent freed-line pairs (cl), which give the hub graph spare
capacity.  Writes every feasible union to OUTDIR/u_<elem>_<j>.txt (flags, cp, cl, size)."""
import sys, os, random, time
sys.path.insert(0, '.')
from sym import *

fn, seed, nel, m, outdir = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
npairs = int(sys.argv[6]) if len(sys.argv) > 6 else 200
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
Mt = Matcher(q, N, lines, lof)
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]
os.makedirs(outdir, exist_ok=True)


def semireg_power(rng):
    """point permutation of order m with all cycles of length m (power of a random element of order divisible by m)."""
    for _ in range(300000):
        M = random_elem(rng)
        pp = perm_points(M, coords, index)
        o = order_of(cycle_type(pp))
        if o % m: continue
        P = list(range(N))
        for _ in range(o // m): P = [pp[x] for x in P]
        if cycle_type(P) == {m: N // m}: return P
    return None


def ucount(U):
    cp = sum(1 for i in range(len(U)) for j in range(i) if Mt.Pm[U[i][0]] >> U[j][0] & 1)
    cl = sum(1 for i in range(len(U)) for j in range(i) if Mt.Lm[U[i][1]] >> U[j][1] & 1)
    return cp, cl


def fstr(U): return ' '.join(f'{p}:{l}' for p, l in U)


for e in range(nel):
    t0 = time.time()
    pp = semireg_power(rng)
    if pp is None: print('no semiregular element found', flush=True); continue
    pl = perm_lines(pp, lines, lidx)
    orbs = flag_orbits(pp, pl, flags_all)
    good = [ob for ob in orbs if len({p for p, _ in ob}) == len(ob) and len({l for _, l in ob}) == len(ob)]
    print('ELEM', e, 'flag orbits', len(orbs), 'valid (distinct pts/lines)', len(good),
          'orbit sizes', sorted({len(o) for o in good}), 'time %.1f' % (time.time() - t0), flush=True)
    feas = []
    for oi, ob in enumerate(good):
        sz, _ = Mt.size(ob)
        if sz == N:
            cp, cl = ucount(ob)
            feas.append((ob, cp, cl))
    print('  feasible single orbits', len(feas), 'time %.1f' % (time.time() - t0), flush=True)
    if len(feas) < 2: continue
    seenpairs = set(); j = 0
    for t in range(npairs):
        (A, cpA, clA), (B, cpB, clB) = rng.sample(feas, 2)
        ps = {p for p, _ in A}; ls = {l for _, l in A}
        if ps & {p for p, _ in B} or ls & {l for _, l in B}: continue
        key = frozenset([tuple(A), tuple(B)])
        if key in seenpairs: continue
        seenpairs.add(key)
        U = A + B
        sz, _ = Mt.size(U)
        cp, cl = ucount(U)
        print('  PAIR try', t, 'k', len(U), 'matching', sz, 'of', N, 'cp', cp, 'cl', cl, flush=True)
        if sz == N:
            with open(os.path.join(outdir, f'u_e{e}_{j}.txt'), 'w') as f:
                f.write(f'k {len(U)} cp {cp} cl {cl} size {sz}\n{fstr(U)}\n')
            print('  FEASIBLE k', len(U), 'cp', cp, 'cl', cl, 'flags', fstr(U), flush=True)
            j += 1
    print('ELEM', e, 'done time %.1f' % (time.time() - t0), flush=True)
