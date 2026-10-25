"""c1: orbit unions of PSL(2,q) on Q(6,q) (binary sextic representation).
For each subgroup H (given by two 2x2 generators):
  - H-orbits on points; an orbit is GOOD iff its rep x is opposite to every other point of its orbit
    (B(x,y) != 0 for y in orbit, y != x), which by invariance is exactly pairwise opposite inside the orbit.
  - orbits O_i, O_j (same H) are COMPATIBLE iff B(rep_i, y) != 0 for all y in O_j.
  - max-weight clique (weight = orbit size) with tools/mwc.py.
Usage: python3 orbits_c1.py Q T [tlimit]
"""
import sys, time, random, itertools, json
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
PROJ = '/home/user/degree-diameter/research/projects/hexagon-family'
sys.path.insert(0, PROJ + '/tools'); sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r1/c1')
from q6lib import Geo, A7, inv_mod
from mwc import max_weight_clique
from sl2rep import gram, sub_matrix

def mm2(x, y, q):
    a, b, c, d = x; e, f, g, h = y
    return ((a * e + b * g) % q, (a * f + b * h) % q, (c * e + d * g) % q, (c * f + d * h) % q)

def canon(x, q):
    return min(x, tuple((-v) % q for v in x))

def closure(gens, q, cap=None):
    I = canon((1, 0, 0, 1), q)
    elems = {I}; frontier = [I]
    while frontier:
        new = []
        for e in frontier:
            for g in gens:
                p = canon(mm2(e, g, q), q)
                if p not in elems:
                    elems.add(p); new.append(p)
                    if cap and len(elems) > cap: return None
        frontier = new
    return frozenset(elems)

def sl2_all(q):
    out = []
    for a, b, c, d in itertools.product(range(q), repeat=4):
        if (a * d - b * c) % q == 1: out.append((a, b, c, d))
    return out

def subgroup_list(q, t, rng, nconj=6):
    """returns list of (name, [gens as 2x2 tuples])"""
    g1 = (1, 1, 0, 1); w = (0, q - 1, 1, 0); g3 = (t % q, 0, 0, pow(t, q - 2, q))
    S = []
    S.append(('G', [g1, w]))
    S.append(('Borel', [g1, g3]))
    S.append(('Dsplit', [g3, w]))           # normalizer of split torus
    # nonsplit torus: companion of x^2 - s x + 1 irreducible
    sq = {(x * x) % q for x in range(q)}
    s = next(s for s in range(q) if all(((s * s - 4 - y * y) % q) != 0 for y in range(q)))  # disc s^2-4 nonsquare
    C = (0, q - 1, 1, s)
    Cinv = (s % q, q - 1, 1, 0)
    z = next(z for z in sl2_all(q) if mm2(mm2(z, C, q), inv_mod_2(z, q), q) == Cinv)
    S.append(('Dnonsplit', [C, z]))
    # small subgroups by random pairs of SL2 elements (A4, S4, A5), distinct up to conjugacy-ish sampling
    allel = sl2_all(q)
    for name, order in [('A4', 12), ('S4', 24), ('A5', 60)]:
        found = {}
        for _ in range(60000):
            x, y = rng.choice(allel), rng.choice(allel)
            H = closure([x, y], q, cap=order)
            if H is not None and len(H) == order:
                found.setdefault(H, (x, y))
            if len(found) >= nconj: break
        for H, (x, y) in found.items():
            S.append((name, [x, y]))
        print('found', name, len(found), file=sys.stderr)
    return S

def inv_mod_2(x, q):
    a, b, c, d = x
    return (d % q, (-b) % q, (-c) % q, a % q)


def heur_clique(w, comp, iters, rng):
    """randomised greedy weighted clique on bool adjacency matrix comp"""
    n = len(w); w = np.asarray(w, dtype=np.float64); best = (0, [])
    nr = np.random.default_rng(rng.randrange(1 << 30))
    for it in range(iters):
        cand = np.ones(n, dtype=bool); chosen = []; tot = 0
        while cand.any():
            idx = np.nonzero(cand)[0]
            score = w[idx] * (1.0 + 0.5 * nr.random(len(idx)))
            v = idx[int(np.argmax(score))]
            chosen.append(int(v)); tot += int(w[v])
            cand &= comp[v]; cand[v] = False
        if tot > best[0]: best = (tot, chosen)
    return best[0], best[1]

def run(q, t, tlimit=60.0, extra_names=None):
    t0 = time.time()
    G = Geo(q); N = G.N
    Gm = gram(q)
    T = G.to_std(Gm); Ti = inv_mod(T, q)
    def perm_of(x):
        M = sub_matrix(*x, q) % q
        return G.perm((T @ M % q) @ Ti % q)
    rng = random.Random(7)
    subs = subgroup_list(q, t, rng)
    print('q=%d: %d subgroups listed (%.1fs)' % (q, len(subs), time.time() - t0), flush=True)
    results = []
    seen_orbit_keys = set()
    pool = []   # (weight, sorted point ids, subgroup name)
    for name, gens in subs:
        if extra_names and name not in extra_names: continue
        perms = [perm_of(x) for x in gens]
        nc, L = connected_components(coo_matrix((np.ones(N * len(perms), dtype=np.int8),
                                                 (np.tile(np.arange(N), len(perms)), np.concatenate(perms))),
                                                shape=(N, N)), directed=True, connection='weak')
        sizes = np.bincount(L, minlength=nc)
        # representative = first point of each orbit
        rep = np.zeros(nc, dtype=np.int64); rep[L[::-1]] = np.arange(N)[::-1]
        rep_of_pt = rep[L]
        Xr = G.C[rep_of_pt]
        vals = ((Xr @ A7) * G.C).sum(1) % q          # B(rep, x)
        notrep = np.arange(N) != rep_of_pt
        badpts = (vals == 0) & notrep
        bad = np.bincount(L, weights=badpts.astype(np.float64), minlength=nc)
        good = np.nonzero(bad == 0)[0]
        # good orbits: all of size > 0 by construction; print summary
        ssz = sizes[good]
        print('  %-9s |orbits|=%d  good=%d  sizes(good)=%s' % (name + str(len(gens)), nc, len(good),
              dict(zip(*np.unique(ssz, return_counts=True)))) if len(good) < 60 else
              '  %-9s |orbits|=%d  good=%d  max good size=%d total good pts=%d' % (name, nc, len(good),
              ssz.max() if len(good) else 0, ssz.sum()), flush=True)
        if len(good) == 0: continue
        if len(good) > 12000:
            print('    skipped: %d good orbits too many for dense compat' % len(good), flush=True); continue
        # compatibility among good orbits (same H): B(rep_i, y) != 0 for all y in O_j
        in_good = np.zeros(nc, dtype=bool); in_good[good] = True
        P = np.nonzero(in_good[L])[0]          # points of good orbits
        LP = L[P]
        gidx = -np.ones(nc, dtype=np.int64); gidx[good] = np.arange(len(good))
        k = len(good)
        comp = np.zeros((k, k), dtype=bool)
        XP = G.C[P]
        for i, oi in enumerate(good):
            r = G.C[rep[oi]]
            v = ((r @ A7) @ XP.T) % q           # B(rep_i, P)
            zero = np.bincount(LP, weights=(v == 0).astype(np.float64), minlength=nc)
            comp[i] = (zero[good] == 0)
        np.fill_diagonal(comp, False)
        comp = comp & comp.T
        w = [int(sizes[o]) for o in good]
        dens = comp.sum() / max(1, k * (k - 1))
        hw, hv = heur_clique(np.array(w), comp, iters=400, rng=rng)
        bw, bv, exact = hw, hv, False
        if k <= 700:
            adj = [0] * k
            for i in range(k):
                bits = 0
                for j in np.nonzero(comp[i])[0]: bits |= (1 << int(j))
                adj[i] = bits
            ew, ev, exact = max_weight_clique(w, adj, tlimit=tlimit)
            if ew >= bw: bw, bv = ew, ev
        print('    compat density %.3f  MWC weight %d (%s) clique orbits %d  (%.1fs)' %
              (dens, bw, 'exact' if exact else 'timeout', len(bv), time.time() - t0), flush=True)
        pts = []
        for i in bv: pts.extend(np.nonzero(L == good[i])[0].tolist())
        pts = sorted(set(pts))
        results.append(dict(sub=name, ngens=len(gens), weight=bw, exact=exact, pts=pts))
        pool.append((name, good, L, sizes))
    return results, G, T, Ti

if __name__ == '__main__':
    q = int(sys.argv[1]); t = int(sys.argv[2]); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 60.0
    names = sys.argv[4].split(',') if len(sys.argv) > 4 else None
    res, G, T, Ti = run(q, t, tl, extra_names=names)
    best = max(res, key=lambda r: r['weight'])
    print('BEST per subgroup:', [(r['sub'], r['weight'], r['exact']) for r in res])
    json.dump([{k: v for k, v in r.items() if k != 'pts'} | {'npts': len(r['pts'])} for r in res],
              open('/home/user/degree-diameter/research/squads/hexfam_r1/c1/summary_q%d.json' % q, 'w'))
    best_pts = best['pts']
    ok, ext = G.check_opp(np.array(best_pts)) if best_pts else (True, 0)
    print('best raw set: sub=%s size=%d pairwise-opp=%s outside-extension-points=%d' % (best['sub'], len(best_pts), ok, ext))
    np.save('/home/user/degree-diameter/research/squads/hexfam_r1/c1/best_raw_q%d.npy' % q, np.array(best_pts))
