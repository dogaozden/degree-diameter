"""Exact (CP-SAT, 1 worker) orbit-union optimum for one representative of each conjugacy class of cyclic subgroups."""
import json, time, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c2')
import orbsolve as O
from verify import verify
cyc = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_subgroups.json'))
cl = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_classes.json'))
TL = float(sys.argv[1])
out = open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyc_results.jsonl', 'a')
order_reps = sorted(cl['reps'], key=lambda i: -cyc[i]['order'])
for i in order_reps:
    g = O.G[cyc[i]['gen']]
    t = time.time()
    r = O.solve([g], tlimit=TL)
    ok = verify(r['T'])[0] if r['T'] else True
    rec = {'type': 'cyclic', 'idx': i, 'order': cyc[i]['order'], 'norb': r['norb'], 'orbit_sizes': r['orbit_sizes'],
           'status': r['status'], 'opt': r['opt'], 'bound': r['bound'], 'verified': ok, 'secs': round(time.time() - t, 1)}
    if r['T']:
        rec['T_example'] = r['T'] if r['opt'] >= 80 else None
    out.write(json.dumps(rec) + '\n'); out.flush()
    print(json.dumps({k: v for k, v in rec.items() if k != 'T_example'}), flush=True)
