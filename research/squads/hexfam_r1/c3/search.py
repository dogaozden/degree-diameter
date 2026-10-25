"""orbit search: subgroups of a cyclic group (and + Frobenius/swap), valid = pairwise opposite orbits,
compatibility = all cross pairs opposite, then max-weight clique. Usage: search.py MODEL q [c a] [minm] [tl]"""
import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r1/c3')
from c3lib import *

HEUR_ITERS = 400

def run(q, model, c=1, a=1, minm=2, tl=60.0, tag=''):
    t0 = time.time()
    if model == 'A':
        G7, gens, N = model_A(q, c, a)
    else:
        G7, gens, N = model_B(q, a)
    geo = Geo(q)
    P = build_perms(geo, G7, gens)
    C = geo.C; Np = geo.N
    W = (C @ A7) % q
    ident = np.arange(Np)
    # ---- candidate orbits per subgroup variant
    variants = []   # (name, lab, k)
    valid = []      # global list: dict(variant index, label, pts, size)
    for m in divisors(N):
        if m < minm:
            continue
        h = perm_pow(P['cyc'], N // m)
        for extra in ([None] + [x for x in gens if x != 'cyc']):
            gl = [h] if extra is None else [h, P[extra]]
            name = 'H%d%s' % (m, '' if extra is None else '+' + extra)
            lab = orbits(Np, gl)
            k = int(lab.max()) + 1
            sizes = np.bincount(lab, minlength=k)
            _, first = np.unique(lab, return_index=True)
            bv = (((C[first[lab]]) * W).sum(1)) % q
            zero = bv == 0
            zero[first] = False
            badcnt = np.bincount(lab[zero], minlength=k)
            vl = np.nonzero(badcnt == 0)[0]
            order = np.argsort(lab, kind='stable'); starts = np.concatenate([[0], np.cumsum(sizes)])
            vi = len(variants)
            variants.append((name, lab, first))
            for L in vl:
                if sizes[L] < 2:
                    continue
                valid.append((vi, int(L), order[starts[L]:starts[L] + sizes[L]], int(sizes[L])))
        print('variant', name if False else '', 'm=%d' % m, 'done', round(time.time() - t0, 1), 'valid so far', len(valid), flush=True)
    K = len(valid)
    print('valid orbits K =', K, flush=True)
    if K == 0:
        return None
    owner = np.concatenate([np.full(len(v[2]), i) for i, v in enumerate(valid)])
    allpts = np.concatenate([v[2] for v in valid])
    # ---- compatibility: orbit i vs orbit j compatible iff no point of j is orthogonal to a point of i
    compat = np.zeros((K, K), dtype=bool)
    byvar = {}
    for i, v in enumerate(valid):
        byvar.setdefault(v[0], []).append(i)
    for vi, idxs in byvar.items():
        name, lab, first = variants[vi]
        for i in idxs:
            L = valid[i][1]
            rep = first[L]
            pperp = np.nonzero(((C[rep] @ A7) % q @ C.T) % q == 0)[0]   # points orthogonal to rep
            bad = np.zeros(int(lab.max()) + 1, dtype=bool)
            bad[lab[pperp]] = True
            mask = bad[lab]
            cnt = np.bincount(owner, weights=mask[allpts].astype(np.float64), minlength=K)
            compat[i] = cnt == 0
    compat &= compat.T
    np.fill_diagonal(compat, False)
    print('compat done', round(time.time() - t0, 1), 'density', round(compat.mean(), 4), flush=True)
    w = [v[3] for v in valid]
    adj = [0] * K
    for i in range(K):
        bits = 0
        for j in np.nonzero(compat[i])[0]:
            bits |= 1 << int(j)
        adj[i] = bits
    from heur import greedy_ls
    hb, hv = greedy_ls(w, compat, iters=HEUR_ITERS, seed=1)
    print('greedy/LS weight', hb, 'orbits', len(hv), flush=True)
    best, verts, exact = max_weight_clique(w, adj, tl)
    if hb > best:
        best, verts, exact = hb, hv, False
    pts = np.concatenate([valid[i][2] for i in verts]) if verts else np.array([], dtype=int)
    print('MWC weight', best, 'exact', exact, 'orbits', len(verts), 'time', round(time.time() - t0, 1), flush=True)
    return best, sorted(int(x) for x in pts)

if __name__ == '__main__':
    q = int(sys.argv[1]); model = sys.argv[2]
    c = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    a = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    minm = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    tl = float(sys.argv[6]) if len(sys.argv) > 6 else 60.0
    res = run(q, model, c, a, minm, tl)
    if res:
        best, pts = res
        fn = '/home/user/degree-diameter/research/squads/hexfam_r1/c3/cand_q%d_%s_c%d_a%d_m%d.txt' % (q, model, c, a, minm)
        open(fn, 'w').write(' '.join(map(str, pts)) + '\n')
        print('WROTE', fn, len(pts))
