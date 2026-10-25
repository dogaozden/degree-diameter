"""c5 refine: exact (step 1) hill-climb from a near-solution state. usage: python3 -I refine.py M BUDGET v1,..,v5 w1,w2"""
import json, random, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c5')
from colour_lift import Q, colouring, hops, base_text, unreached  # noqa: E402

M = int(sys.argv[1]); budget = float(sys.argv[2])
v = [0] + [int(x) for x in sys.argv[3].split(',')]
w = [int(x) for x in sys.argv[4].split(',')]
cl = colouring(2); s1, s2 = hops(2)          # same instance as search.py pool entry seed 2
rng = random.Random(99)
cur = unreached(base_text(M, cl, v, w, s1, s2), 1)
print('start', cur, v, w, flush=True)
t_end = time.time() + budget; evals = 0
while cur > 0 and time.time() < t_end:
    nv, nw = list(v), list(w)
    k = rng.randrange(Q + 2)
    if k < Q:
        nv[k + 1] = (nv[k + 1] + rng.choice((-1, 1, 2, -2))) % M if rng.random() < 0.7 else rng.randrange(M)
    else:
        j = k - Q
        nw[j] = (nw[j] + rng.choice((-1, 1, 2, -2))) % M if rng.random() < 0.7 else rng.randrange(M)
    new = unreached(base_text(M, cl, nv, nw, s1, s2), 1); evals += 1
    if new <= cur:
        v, w, cur = nv, nw, new
        print('accept', cur, v, w, round(time.time() - t_end + budget, 1), flush=True)
rec = {'M': M, 'full_unreached': cur, 'v': v, 'w': w, 'colouring_seed': 2, 'hops_seed': 2, 'evals': evals}
print(json.dumps(rec), flush=True)
with open('/home/user/degree-diameter/research/squads/r1-d8/c5/search_log.jsonl', 'a') as fh:
    fh.write(json.dumps(rec) + '\n')
