import sys, os, time, random, pickle, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from starlib import *
seed = int(sys.argv[1]); secs = float(sys.argv[2]); nT = int(sys.argv[3]); nM = int(sys.argv[4])
rng = random.Random(seed); outd = sys.argv[5]; os.makedirs(outd, exist_ok=True)
rows = []
for f in sys.argv[6:]:
    rows += pickle.load(open(f, 'rb'))
rows = [r for r in rows if r['gm'] == 0]
rows.sort(key=lambda r: (-r['usable'] + 2 * r['Tperp']))
print('candidate T lines', len(rows), flush=True)
best_all = (-1e9, None)
t0 = time.time()
def run_T(row, M, pool_lines, Pdata):
    """pool_lines: list of line ids through points of M (not in S); Pdata: their (conc, D4)"""
    T = np.array(row['T']); m = row['m']
    bcode = base_T_codes(T)                       # per base point: -1 (T-perp) or index 0..11
    nb_idx = collections.Counter(bcode.tolist())   # counts of base classes
    usable_T = [i for i in range(12) if row['usable'] and (not (H.collinear_points(int(T[i])) & set(R.tolist())))]
    U = usable_T
    nb_single = {i: nb_idx.get(i, 0) for i in range(12)}; nb_perp = nb_idx.get(-1, 0); nb_empty = 0
    return U, nb_single, nb_perp
for trial in range(nT):
    row = rows[trial % len(rows)] if rows else None
    if row is None: break
    T = np.array(row['T']); m = row['m']
    Rset = set(R.tolist())
    U = [i for i in range(12) if not (H.collinear_points(int(T[i])) & Rset)]
    bcode = base_T_codes(T)
    nb = collections.Counter(bcode.tolist())
    nperp = nb.get(-1, 0)
    # M choice loop
    for mi in range(nM):
        while True:
            M = rng.randrange(N)
            if not inS[M] and not (H.lines_meeting(M) & set(S.tolist())) == set(): break
        # lines meeting M, pool
        pts = H.lp[M]
        pool = []
        for p in pts:
            for L in H.pl[p]:
                if L != M and not inS[L]: pool.append(int(L))
        pool = list(dict.fromkeys(pool))
        pdat = {}
        for L in pool: pdat[L] = profile(L)
        # point on M of each pool line
        pM = {L: [int(p) for p in H.lp[L] if p in set(pts.tolist())][0] for L in pool}
        conc_M = profile(M)[0]
        excluded0 = set(conc_M.tolist())
        # SA over the star
        def evaluate(assign):
            # assign: dict tindex -> line id
            X = sorted(assign)
            if not X: return 0, None
            excl = set(excluded0)
            for t in X: excl |= set(pdat[assign[t]][0].tolist())
            usable = np.ones(len(S), bool); usable[list(excl)] = False
            codes = np.zeros(len(S), np.int64)
            for b, t in enumerate(X):
                codes |= pdat[assign[t]][1].astype(np.int64) << b
            # base codes: position-in-X bits
            xmask = (1 << len(X)) - 1
            pos = {t: b for b, t in enumerate(X)}
            ns = collections.Counter(codes[usable].tolist())
            nbc = collections.Counter()
            for t in range(12):
                if t in pos: nbc[1 << pos[t]] += nb.get(t, 0)
            nbc[xmask] += nb.get(-1, 0)
            nbc[0] += sum(v for k2, v in nb.items() if k2 >= 0 and k2 not in pos)
            deficit = sum(max(0, nbc[c] - ns.get(c, 0)) for c in nbc)
            return len(X) - deficit, deficit
        # greedy random init + SA
        assign = {}; usedp = set()
        cur_f = 0; best = (-1e9, None)
        T_sa = 0.4; it = 0
        tstart = time.time()
        Ulist = U[:]
        while time.time() - tstart < secs / nM:
            it += 1
            mv = rng.random()
            new = dict(assign)
            if mv < 0.4 and len(new) < len(Ulist):
                t = rng.choice([x for x in Ulist if x not in new])
                cands = [L for L in pool if pM[L] not in {pM[v] for v in new.values()}]
                if not cands: continue
                new[t] = rng.choice(cands)
            elif mv < 0.6 and new:
                t = rng.choice(list(new)); del new[t]
            else:
                if not new: continue
                t = rng.choice(list(new))
                used = {pM[v] for k2, v in new.items() if k2 != t}
                cands = [L for L in pool if pM[L] not in used]
                if not cands: continue
                new[t] = rng.choice(cands)
            f2, dfc = evaluate(new)
            if f2 >= cur_f or rng.random() < pow(2.718, (f2 - cur_f) / T_sa):
                assign = new; cur_f = f2
                if f2 > best[0]: best = (f2, dict(assign), dfc)
        if best[1] is not None:
            print(f'T {trial} M {M} best F {best[0]} k {len(best[1])} deficit {best[2]} it {it}', flush=True)
            if best[0] > best_all[0]:
                best_all = (best[0], dict(row=row['T'], m=m, M=M, assign=best[1]))
print('overall best', best_all[0], flush=True)
pickle.dump(best_all, open(os.path.join(outd, 'best_star.pkl'), 'wb'))
