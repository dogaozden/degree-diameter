"""Local search on sigma (swap moves) for K=82 with R = record R + [x0], hub graph = record hub graph + one 4-regular pair.
Objective: ordered bad pairs at distance > 7 (count7). Accept if not worse. Usage: ls82.py X0 SECONDS SEED"""
import sys, time, random, subprocess
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c4')
from exp2 import *
x0 = int(sys.argv[1]); secs = float(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
hubK = add_hub_pair(hub0, K0, random.Random(1))
R1 = R0 + [x0]
tag = f'ls_{x0}_{sys.argv[3]}'
fn = f'/home/user/degree-diameter/research/squads/conics2-r1/c4/{tag}.edges'
def score(s):
    n, E = build(q, N, LP, s, R1, hubK, K0 + 1, K0 + 1)
    write_edges(fn, n, E)
    out = subprocess.run(['./count7', fn, '7'], capture_output=True, text=True).stdout
    return int(out.split('bad_ordered_pairs=')[1].split()[0])
cur = sig.copy(); best = score(cur); start = best
print('start', best, flush=True)
t0 = time.time(); it = 0; acc = 0
# near moves: partners within incidence distance 2 of x0 (points sharing a line), else random
near = set()
for l in PL[x0]:
    for p in LP[l]:
        near.add(int(p))
        for l2 in PL[p]:
            for p2 in LP[l2]: near.add(int(p2))
near = sorted(near)
while time.time() - t0 < secs:
    it += 1
    p = rng.choice([x0] + near) if rng.random() < 0.7 else rng.randrange(N)
    y = rng.choice(near) if rng.random() < 0.7 else rng.randrange(N)
    if p == y: continue
    cur[p], cur[y] = cur[y], cur[p]
    s = score(cur)
    if s <= best:
        if s < best: print('it', it, 'improved', s, flush=True)
        if s < best: acc += 1
        best = s
        if best == 0: break
    else:
        cur[p], cur[y] = cur[y], cur[p]
print('done iters', it, 'start', start, 'best', best, 'improving moves', acc, flush=True)
if best == 0 or True:
    with open(f'/home/user/degree-diameter/research/squads/conics2-r1/c4/best_{tag}.sig', 'w') as f:
        f.write('\n'.join(map(str, cur.tolist())) + '\n')
    with open(f'/home/user/degree-diameter/research/squads/conics2-r1/c4/best_{tag}.R', 'w') as f:
        f.write(' '.join(map(str, R1)) + '\n')
