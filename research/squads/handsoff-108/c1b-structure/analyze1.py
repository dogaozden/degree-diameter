import numpy as np, sys
N = {'psl': 588984, 'prod': 592704}
def load(fn):
    tags, rows, ords = [], [], []
    for line in open(fn):
        f = line.rstrip('\n').split('\t')
        if len(f) < 12: continue
        tags.append(f[0]); rows.append([int(x) for x in f[1:11]])
        ords.append([int(x) for x in f[11:21]])
    return tags, np.array(rows, dtype=float), np.array(ords)
def auc(pos, neg):
    # P(pos > neg) with ties counted half (Mann-Whitney)
    allv = np.concatenate([pos, neg]); r = allv.argsort().argsort() + 1.0
    # average ranks for ties
    from collections import defaultdict
    _, inv, cnt = np.unique(allv, return_inverse=True, return_counts=True)
    csum = np.cumsum(cnt); avg = csum - (cnt - 1) / 2.0
    rk = avg[inv]
    npos = len(pos); nneg = len(neg)
    return (rk[:npos].sum() - npos * (npos + 1) / 2) / (npos * nneg)
def feats(rows, ords, grp):
    # columns: energy, plain, fixm, lev0..lev6 (lev[h] = ball size at distance h+1 on its side)
    E = rows[:, 0]; P = rows[:, 1]; F = rows[:, 2]; L = rows[:, 3:10]
    o = ords[:, 1:]   # the 9 non-e letters
    d = {}
    d['energy'] = E; d['plain'] = P; d['fixm'] = F
    for h in range(7): d['lev%d' % (h + 1)] = L[:, h]
    d['U5=N-lev5'] = N[grp] - L[:, 4]
    d['U3=N-lev3'] = N[grp] - L[:, 2]
    d['U4=N-lev4'] = N[grp] - L[:, 3]
    d['U6=N-lev6'] = N[grp] - L[:, 5]
    d['n_inv'] = (o == 2).sum(1); d['n_ord3'] = (o == 3).sum(1); d['n_ord4'] = (o == 4).sum(1)
    d['n_ord6'] = (o == 6).sum(1); d['n_ordgt6'] = (o > 6).sum(1)
    d['orbit_inv_pairs'] = ((o == 2).sum(1))
    return d
if __name__ == '__main__':
    grp = sys.argv[1]
    t, R, O = load('stats_rand_%s.tsv' % grp)
    tg, G, OG = load('stats_good_%s.tsv' % grp)
    tc, C, OC = load('stats_ce_%s.tsv' % grp)
    dr, dg, dc = feats(R, O, grp), feats(G, OG, grp), feats(C, OC, grp)
    print('group', grp, 'random n=%d good n=%d chain-ends n=%d' % (len(R), len(G), len(C)))
    print('random energy: min %d p1 %d p10 %d median %d' % tuple(np.percentile(dr['energy'], [0, 1, 10, 50]).astype(int)))
    print('random plain min/p1/median', np.percentile(dr['plain'], [0, 1, 50]))
    print('chain-end energy values:', np.unique(dc['energy'], return_counts=True))
    print('%-14s %8s %8s %8s %8s %8s | %9s %9s' % ('feature', 'rand_med', 'rand_p1', 'good_med', 'ce_med', 'corrRand', 'AUC good', 'AUC ce'))
    for k in dr:
        if k in ('energy', 'plain'): pass
        rv, gv, cv = dr[k], dg[k], dc[k]
        # Spearman-like correlation with energy among random sets
        cor = np.corrcoef(rv.argsort().argsort(), dr['energy'].argsort().argsort())[0, 1] if rv.std() > 0 else float('nan')
        a_g = auc(gv, rv) if gv.std() + rv.std() > 0 else float('nan')
        a_c = auc(cv, rv) if cv.std() + rv.std() > 0 else float('nan')
        print('%-14s %8.1f %8.1f %8.1f %8.1f %8.3f | %9.3f %9.3f' % (k, np.median(rv), np.percentile(rv, 1), np.median(gv), np.median(cv), cor, a_g, a_c))
