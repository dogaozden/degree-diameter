"""c5 search: hill-climb over colour voltages v_1..v_q (v_0 = 0 by switching) and hop voltages w_1, w_2 in Z_M.

usage: python3 -I search.py STEP BUDGET_SECONDS M1,M2,...
Cost = liftdiam unreached pairs at source step STEP (D = 8).  A candidate with cost 0 is confirmed with step 1.
Stops at the first M that cannot be closed within the budget.
"""
import json
import random
import sys
import time

sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c5')
from colour_lift import Q, N, colouring, hops, base_text, unreached, check_colouring  # noqa: E402

PERM = None

OUT = '/home/user/degree-diameter/research/squads/r1-d8/c5/search_log.jsonl'


def log(rec):
    with open(OUT, 'a') as fh:
        fh.write(json.dumps(rec) + '\n')
    print(json.dumps(rec), flush=True)


def run_M(M, budget, step, rng, pool):
    t_end = time.time() + budget
    evals = 0
    while time.time() < t_end:
        ci = rng.randrange(len(pool))
        classes, s1, s2 = pool[ci]
        v = [0] + [rng.randrange(M) for _ in range(Q)]
        w = [rng.randrange(M), rng.randrange(M)]
        cur = unreached(base_text(M, classes, v, w, s1, s2, PERM), step)
        evals += 1
        stall = 0
        while time.time() < t_end and cur > 0 and stall < 50:
            nv, nw = list(v), list(w)
            k = rng.randrange(Q + 2)
            if k < Q:
                if rng.random() < 0.5:
                    nv[k + 1] = (nv[k + 1] + rng.choice((-1, 1))) % M
                else:
                    nv[k + 1] = rng.randrange(M)
            else:
                j = k - Q
                if rng.random() < 0.5:
                    nw[j] = (nw[j] + rng.choice((-1, 1))) % M
                else:
                    nw[j] = rng.randrange(M)
            new = unreached(base_text(M, classes, nv, nw, s1, s2, PERM), step)
            evals += 1
            if new <= cur:
                if new < cur:
                    stall = 0
                else:
                    stall += 1
                v, w, cur = nv, nw, new
            else:
                stall += 1
        if cur == 0:
            return v, w, ci, evals, True
    return None, None, None, evals, False


def main():
    step = int(sys.argv[1])
    budget = float(sys.argv[2])
    Ms = [int(x) for x in sys.argv[3].split(',')]
    seeds = [1, 2, 3]
    pool = []
    for s in seeds:
        cl = colouring(s)
        check_colouring(cl)
        s1, s2 = hops(s)
        pool.append((cl, s1, s2))
    print('pool ready', flush=True)
    rng = random.Random(12345)
    global PERM
    PERM = list(range(2 * N)); random.Random(777).shuffle(PERM)
    for M in Ms:
        t0 = time.time()
        v, w, ci, evals, ok = run_M(M, budget, step, rng, pool)
        if not ok:
            log({'M': M, 'step': step, 'closed_at_step': False, 'evals': evals, 'secs': round(time.time() - t0, 1)})
            break
        full = unreached(base_text(M, pool[ci][0], v, w, pool[ci][1], pool[ci][2], None), 1)
        log({'M': M, 'step': step, 'closed_at_step': True, 'full_unreached': full, 'v': v, 'w': w, 'colouring_seed': seeds[ci],
             'evals': evals, 'secs': round(time.time() - t0, 1)})
        if full != 0:
            break


if __name__ == '__main__':
    main()
