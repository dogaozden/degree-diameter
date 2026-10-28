import sys, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c2')
from sat_model import solve_atleast
from verify import verify
k = int(sys.argv[1]); out = sys.argv[2]
t0 = time.time()
T = solve_atleast(k, solver=sys.argv[3] if len(sys.argv) > 3 else 'cd15')
print('k', k, 'time', round(time.time()-t0,1), 'result', None if T is None else len(T), flush=True)
if T is not None:
    print(verify(T), flush=True)
    json.dump(sorted(T), open(out, 'w'))
