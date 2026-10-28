import sys, time, json
from setup_common import *
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
from pysat.card import CardEnc, EncType
NL = G.nl
con = G.con
oset = set(OV)
# concurrent pairs with their meeting point
meet = {}
for z in range(N):
    ls = [l for l in range(NL) if G.I[z, l]]
    for i in range(len(ls)):
        for j in range(i+1, len(ls)):
            meet[(ls[i], ls[j])] = z

def solve(mode, cap_pairs=None, tlimit=600):
    """mode 'spread': pairwise non-concurrent. mode 'pencil': matching of concurrent pairs meeting off the ovoid,
    no third R-line meets a pair. cap_pairs: at most this many concurrent pairs."""
    w = WCNF()
    top = NL
    for (l, m), z in meet.items():
        if mode == 'spread' or z in oset:
            w.append([-(l+1), -(m+1)])
        else:
            for n in set(np.nonzero(con[l] | con[m])[0]) - {l, m}:
                w.append([-(l+1), -(m+1), -(int(n)+1)])
    if cap_pairs is not None:
        # p_lm <-> x_l & x_m ; at most cap_pairs p's
        pv = []
        for (l, m), z in meet.items():
            if mode == 'pencil' and z not in oset:
                top += 1; p = top
                w.append([-p, l+1]); w.append([-p, m+1]); w.append([p, -(l+1), -(m+1)])
                pv.append(p)
        enc = CardEnc.atmost(lits=pv, bound=cap_pairs, top_id=top, encoding=EncType.seqcounter)
        for c in enc.clauses: w.append(c)
    for l in range(NL):
        w.append([l+1], weight=1)
    t = time.time()
    with RC2(w) as rc2:
        mdl = rc2.compute()
        S = [l for l in range(NL) if mdl[l] > 0]
    return S, time.time()-t

def pairs_of(S):
    s = set(S)
    return [(l, m, z) for (l, m), z in meet.items() if l in s and m in s]

if __name__ == '__main__':
    res = {}
    S, t = solve('spread')
    assert is_partial_spread(G, S)
    print('max partial spread of Q(4,5): %d (%.1fs)' % (len(S), t), flush=True)
    res['spread'] = S
    S, t = solve('pencil')
    prs = pairs_of(S)
    print('relaxed, no cap: %d lines, %d pairs, pair points on ovoid: %d (%.1fs)' % (len(S), len(prs), sum(1 for p in prs if p[2] in oset), t), flush=True)
    res['pencil_nocap'] = S
    S, t = solve('pencil', cap_pairs=13)
    prs = pairs_of(S)
    print('relaxed, <=13 pairs: %d lines, %d pairs (%.1fs)' % (len(S), len(prs), t), flush=True)
    res['pencil_cap13'] = S
    json.dump({k: [int(x) for x in v] for k, v in res.items()}, open('maxsets_q5.json', 'w'))
