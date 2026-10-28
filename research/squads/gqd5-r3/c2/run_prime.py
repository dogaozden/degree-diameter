"""Exact-or-best orbit-union search (CP-SAT, 1 worker) for one representative of each prime-order symmetry class
of the full spread stabiliser Aut_S (order 3542880). Any symmetric relaxed set is invariant under a subgroup of prime
order, so the largest value over these 9 classes bounds every symmetric construction (see primeorders.py)."""
import json, time, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c2')
import numpy as np
import orbsolve as O
from verify import verify
reps = json.load(open('prime_reps.json'))
TL = float(sys.argv[1]); which = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else range(len(reps))
out = open('prime_results.jsonl', 'a')
for i in which:
    r0 = reps[i]
    g = np.array(r0['perm'], dtype=np.int64)
    t = time.time()
    r = O.solve([g], tlimit=TL)
    ok = verify(r['T'])[0] if r['T'] else True
    rec = {'class': i, 'order': r0['order'], 'ptype': r0['ptype'], 'fixedS': r0['fixedS'], 'norb': r['norb'],
           'orbit_sizes': r['orbit_sizes'], 'status': r['status'], 'best_found': r['opt'], 'bound': r['bound'],
           'verified': ok, 'secs': round(time.time() - t, 1)}
    if r['T']:
        rec['T'] = r['T']
    out.write(json.dumps(rec) + '\n'); out.flush()
    print(json.dumps({k: v for k, v in rec.items() if k != 'T'}), flush=True)
