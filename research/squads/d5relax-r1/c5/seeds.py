"""Card c5 (squad d5relax-r1): seeded growth from structured partial ovoids / torus orbit unions.
Builds seed sets for W(11) (numbering of theorems/d5relax/orbits.WSp(11)), extends each greedily to a maximal
relaxed set, and writes rtabu-format start files (size line, then points)."""
import sys, os, json, random, time
import numpy as np
D = '/home/user/degree-diameter/research/theorems/d5relax'
sys.path.insert(0, D)
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c10')
from orbits import WSp, orbits_of
import highspy

HERE = os.path.dirname(os.path.abspath(__file__))
q = 11
W = WSp(q)
C = W.C
n = W.n


def relaxed(T):
    T = np.array(sorted(set(int(x) for x in T)), dtype=np.int64)
    d = C[np.ix_(T, T)].sum(1)
    return bool((d <= 1).all())


def extend(S, rng, mode='pair'):
    """greedy: add points keeping the set relaxed.  mode 'pair' prefers points collinear with exactly one point
    of S that is itself single (creates a pair); mode 'free' prefers points with no S-neighbour.  Ties: fewest
    feasible neighbours (min damage), random."""
    inS = np.zeros(n, bool); inS[list(S)] = True
    while True:
        dS = C[:, inS].sum(1)
        deg = np.zeros(n, int)
        Sl = np.nonzero(inS)[0]
        deg[Sl] = C[np.ix_(Sl, Sl)].sum(1)
        singles = inS & (deg == 0)
        sc = C[:, singles].sum(1)
        feas = (~inS) & ((dS == 0) | ((dS == 1) & (sc == 1)))
        if not feas.any():
            break
        F = np.nonzero(feas)[0]
        pairc = F[dS[F] == 1] if mode == 'pair' else np.array([], int)
        freec = F[dS[F] == 0]
        cand = pairc if (mode == 'pair' and len(pairc)) else (freec if len(freec) else pairc)
        if len(cand) == 0:
            cand = F
        dmg = C[np.ix_(cand, F)].sum(1)
        m = dmg.min()
        best = cand[dmg == m]
        x = int(best[rng.randrange(len(best))])
        inS[x] = True
    return sorted(np.nonzero(inS)[0].tolist())


def write_start(path, T):
    with open(path, 'w') as f:
        f.write('%d\n' % len(T))
        for v in T:
            f.write('%d\n' % v)


if __name__ == '__main__':
    t0 = time.time()
    rng = random.Random(5)
    seeds = {}
    # (1) old 87-point relaxed set and (2) gqd5-r2 c2 best_T11 (identical sets, checked)
    seeds['w87'] = json.load(open('/home/user/degree-diameter/research/theorems/d5gq/graphs/W11_relaxed_set_87.json'))
    # (3) Lemma 1.3 partial ovoid (3q-1 = 32 points), built by family.py and mapped with WSp.index
    from family import family_points
    P = np.array(family_points(q), dtype=np.int64)
    fam = sorted(W.index(P).tolist())
    seeds['family'] = fam
    print('family: %d points, relaxed %s, pairs %d' % (len(fam), relaxed(fam), C[np.ix_(fam, fam)].sum() // 2))
    # (4) unions of torus orbits: diag(a,b,a^-1,b^-1), cyclic subgroups; MIP over orbit unions with <= 4 orbits
    inv = W.inv; mul = W.mul
    def torus_perm(a, b):
        d = np.array([a, b, inv[a], inv[b]])
        X = mul[W.P, d[None, :]]
        return W.index(X)
    best_torus = (0, None, None)
    tried = 0
    pairs_ab = [(a, b) for a in range(2, q) for b in range(2, q)]
    rng.shuffle(pairs_ab)
    for (a, b) in pairs_ab[:40]:
        g = torus_perm(a, b)
        lab, k = orbits_of([g], n)
        if k > 320 or k < 40:
            print('skip diag(%d,%d): %d orbits' % (a, b, k)); continue
        sizes = np.bincount(lab, minlength=k)
        rep = np.array([np.nonzero(lab == i)[0][0] for i in range(k)])
        N = np.zeros((k, k), dtype=np.int64)
        for i in range(k):
            N[i] = np.bincount(lab[C[rep[i]]], minlength=k)
        ok = [i for i in range(k) if N[i, i] <= 1]
        if not ok:
            continue
        h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', 4.0)
        h.setOptionValue('threads', 1)
        m = len(ok); inf = highspy.kHighsInf
        for _ in ok: h.addVar(0.0, 1.0)
        h.changeColsIntegrality(m, np.arange(m, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * m))
        h.changeColsCost(m, np.arange(m, dtype=np.int32), -sizes[ok].astype(float))
        for aa, i in enumerate(ok):
            row = N[i, ok].astype(float); S = row.sum()
            if S > 1:
                coef = row.copy(); coef[aa] += S - 1
                idx = np.nonzero(coef)[0]
                h.addRow(-inf, S, len(idx), idx.astype(np.int32), coef[idx])
        # cardinality: at most 4 orbits
        h.addRow(-inf, 4.0, m, np.arange(m, dtype=np.int32), np.ones(m))
        h.run()
        sol = h.getSolution().col_value
        I = [ok[t] for t in range(m) if sol[t] > 0.5]
        T = sorted(np.nonzero(np.isin(lab, I))[0].tolist())
        tried += 1
        print('torus diag(%d,%d,%d,%d): %d orbits, %d relaxed-eligible, union of %d orbits = %d pts, relaxed %s'
              % (a, b, inv[a], inv[b], k, m, len(I), len(T), relaxed(T)))
        if len(T) > best_torus[0]:
            best_torus = (len(T), T, (a, b))
    seeds['torus'] = best_torus[1] if best_torus[1] else [0]
    print('torus best union: %d points, (a,b)=%s, tried %d' % (best_torus[0], best_torus[2], tried))

    # greedy extension of each seed, several random restarts; keep the best extended set per seed
    results = {}
    for name, S in seeds.items():
        assert relaxed(S), name
        if len(S) == 0: continue
        bestT = None
        for r in range(12):
            mode = 'pair' if r % 2 == 0 else 'free'
            T = extend(S, rng, mode)
            if bestT is None or len(T) > len(bestT[0]):
                bestT = (T, mode)
        T, mode = bestT
        d = C[np.ix_(T, T)].sum(1)
        print('extend %-8s seed %3d -> %3d (mode %s, pairs %d, relaxed %s)  [%.0f s]'
              % (name, len(S), len(T), mode, d.sum() // 2, relaxed(T), time.time() - t0))
        results[name] = (len(T), T)
        write_start(os.path.join(HERE, 'start_%s.txt' % name), T)
    json.dump({k: v[1] for k, v in results.items()}, open(os.path.join(HERE, 'extended.json'), 'w'))
