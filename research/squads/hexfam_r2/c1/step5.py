import sys, time, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from evalgrp import *
t0 = time.time()
res = pickle.load(open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/step4_results.pkl', 'rb'))
top = [r[1] for r in res[:6]]
variants = [('none', [])] + [(k, [EXTRA[k]]) for k in EXTRA]
best = (0, None, None, None)
rows = []
for sub in top:
    for vn, ex in variants:
        r = evaluate([PERMS[n] for n in sub] + ex, tl=8, kmax=3000)
        if r.get('skip'):
            rows.append((sub, vn, 'skip K=%d' % r['K'])); continue
        rows.append((sub, vn, r['K'], r['good'], r['best'], r['exact']))
        if r['best'] > best[0]:
            S = np.nonzero(np.isin(r['lab'], r['chosen']))[0]
            best = (r['best'], sub, vn, S)
            print('BEST', r['best'], sub, vn, 'K', r['K'], 'good', r['good'], 'exact', r['exact'], round(time.time()-t0,1), flush=True)
for row in rows: print(row, flush=True)
if best[3] is not None:
    S = best[3]
    ok = is_ncol(S)
    print('best size', len(S), 'ncol', ok)
    open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/best_step5.txt', 'w').write(' '.join(map(str, S.tolist())) + '\n')
    pickle.dump(best, open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/best_step5.pkl', 'wb'))
print('time', round(time.time()-t0,1))
