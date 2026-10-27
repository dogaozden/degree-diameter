import sys, time, collections, itertools, random, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from evalgrp import *
t0 = time.time()
results = []
best_overall = (0, None, None)
combos = [c for k in (2, 3) for c in itertools.combinations(RN, k)]
print('subsets', len(combos), flush=True)
for c in combos:
    r = evaluate([PERMS[n] for n in c], tl=3)
    if r.get('skip'): continue
    results.append((r['best'], c, r['K'], r.get('good', 0), r.get('gsizes', [])))
    if r['best'] > best_overall[0]:
        best_overall = (r['best'], c, r.get('chosen'))
        print('NEW BEST', r['best'], c, 'K', r['K'], 'good', r['good'], r['gsizes'], round(time.time()-t0,1), flush=True)
results.sort(reverse=True)
print('top 15:')
for x in results[:15]: print(x, flush=True)
print('time', round(time.time()-t0,1))
pickle.dump(results, open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/step4_results.pkl', 'wb'))
