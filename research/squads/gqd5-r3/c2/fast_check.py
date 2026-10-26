import sys, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c2')
import orbsolve as O
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c2'); from verify import verify
cyc = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_subgroups.json'))
for idx in map(int, sys.argv[1:]):
    g = O.G[cyc[idx]['gen']]
    r = O.solve([g])
    ok = verify(r['T'])
    print(idx, cyc[idx]['order'], {k: v for k, v in r.items() if k != 'T'}, ok, flush=True)
