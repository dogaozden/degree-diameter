#!/usr/bin/env python3
"""Card c16: Weyl-distance graphs of finite buildings, extended scan (max degree 20, diameter up to 12).
Reuses the functions of research/theorems/squad165/weyl_graphs.py (read only).
Writes c16/records.jsonl (one line per union X with exact diameter <= MAXD) and a progress log.
Usage: timeout 900 nice -n 10 python3 -u scan16.py"""
import sys, json, itertools, time, os
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/squad165')
import numpy as np
import weyl_graphs as W

MAXDEG, MAXD, MINORDER = 20, 12, 500
MAXX = int(os.environ.get('C16_MAXX', '4000'))
ONLY = os.environ.get('C16_ONLY', '')
TIME_LIMIT = float(os.environ.get('C16_TLIM', '780'))
HERE = os.path.dirname(os.path.abspath(__file__))
t0 = time.time()

blds = W.buildings()
extra = []
for qq in (17, 19):
    extra.append((f'A2({qq})', 'A', 2, [qq] * 2))
    extra.append((f'B2/C2({qq})', 'B', 2, [qq, qq]))
    extra.append((f'G2({qq})', 'G', 2, [qq, qq]))
    extra.append((f'A3({qq})', 'A', 3, [qq] * 3))
blds += extra
if ONLY:
    blds = [b for b in blds if b[0] in ONLY.split(',')]

out = open(os.path.join(HERE, os.environ.get('C16_OUT', 'records.jsonl')), 'w')
best = {}   # (dm, D) -> record with max order
cache = {}
stop = False
for name, t, n, params in blds:
    if time.time() - t0 > TIME_LIMIT:
        print('time limit reached before', name, flush=True); break
    key = (t, n)
    if key not in cache:
        cache[key] = W.Coxeter(t, n)
    C = cache[key]
    q = C.qw(params)
    PW = int(sum(q))
    subsets = [K for r in range(n) for K in itertools.combinations(range(n), r)]
    PK = {K: int(sum(q[np.nonzero(C.parabolic(K))[0]])) for K in subsets}
    side = {K: PW // PK[K] for K in subsets}
    good = [K for K in subsets if side[K] <= W.moore_side(MAXDEG, MAXDEG)]
    for I in good:
        for J in good:
            if side[I] + side[J] < MINORDER:
                continue
            dcs = C.double_cosets(I, J)
            ND = [int(sum(q[np.nonzero(S)[0]])) for (w, S) in dcs]
            budget = MAXDEG * min(PK[I], PK[J])
            cand = sorted([k for k in range(len(dcs)) if ND[k] <= budget], key=lambda k: ND[k])
            count = 0
            stack = [((), 0, 0)]
            while stack:
                X, NX, start = stack.pop()
                if X:
                    dA, dB = NX // PK[J], NX // PK[I]
                    if dA <= MAXDEG and dB <= MAXDEG and side[I] <= W.moore_side(dA, dB) and \
                            side[J] <= W.moore_side(dB, dA):
                        count += 1
                        if count > MAXX:
                            break
                        reps = [dcs[k][0] for k in X]
                        inv = [int(C.inv[y]) for y in reps]
                        eA = W.ecc_side(C, C.parabolic(I), reps, inv, I, J, maxsteps=2 * MAXD)
                        eB = W.ecc_side(C, C.parabolic(J), inv, reps, J, I, maxsteps=2 * MAXD)
                        vals = list(eA) + list(eB)
                        if all(v is not None for v in vals):
                            D = max(vals)
                            if D <= MAXD:
                                order = side[I] + side[J]
                                dm = max(dA, dB)
                                words = [''.join(str(i + 1) for i in C.word[y]) or 'e' for y in reps]
                                rec = dict(building=name, I=list(I), J=list(J), X=words, dA=dA, dB=dB,
                                           dmax=dm, D=D, order=order, sides=[side[I], side[J]])
                                out.write(json.dumps(rec) + '\n')
                                key2 = (dm, D)
                                if key2 not in best or best[key2]['order'] < order:
                                    best[key2] = rec
                for k in range(start, len(cand)):
                    kk = cand[k]
                    if NX + ND[kk] > budget:
                        break
                    stack.append((X + (kk,), NX + ND[kk], k + 1))
            if count > MAXX:
                print('  truncated', name, I, J, flush=True)
    out.flush()
    print('done', name, 'P_W', PW, 'elapsed %.0f' % (time.time() - t0), flush=True)
out.close()
json.dump([[k[0], k[1], v] for k, v in sorted(best.items())], open(os.path.join(HERE, os.environ.get('C16_OUT', 'records.jsonl') + '.best.json'), 'w'), indent=0)
print('finished elapsed %.0f' % (time.time() - t0), flush=True)
