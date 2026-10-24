#!/usr/bin/env python3
"""Card d3: Z_5 x Z_k colour-voltage lifts of H(5).

Base B = H(5) + two random point->line bijections s_1, s_2 (hops), 2N = 7812 vertices, degree 8.
Flags: edge-coloured by q+1 = 6 perfect matchings (colour c = matching c). A flag of colour c has voltage
(0, v_c) with v_0 = 0 (w.l.o.g. by switching: a global shift of all point->line darts).
Hop h at point p has voltage (h, W_h[cls(p)]), cls = point class (1 class = constant hop voltage).
Group Z_5 x Z_k (liftdiam header 'NB 5 k E'), M = 5k.  Score = liftdiam unreached pairs at D = 8.

usage: python3 -B -I z5k.py K MODE SEEDS BUDGET SCREEN_STEP
   K: k in Z_5 x Z_k.  MODE: const | cls2 | cls3 (number of point classes for the hop voltages).
   SEEDS: comma list; seed s fixes colouring s, hops s, point classes s.
   BUDGET: seconds of search per seed.  SCREEN_STEP: liftdiam source stride used for the search.
   Any candidate with 0 unreached at the screen step is re-checked at SRC_STEP 1 (exact).
"""
import json
import os
import random
import subprocess
import sys
import time

D8 = '/home/user/degree-diameter/research/theorems/d8'
HERE = os.path.dirname(os.path.abspath(__file__))
LIFTDIAM = os.path.join(D8, 'liftdiam')
sys.path.insert(0, D8)
import gh  # noqa: E402
from models import perfect_matching  # noqa: E402

Q = 5
M1 = 5
H = gh.load(Q)
N = H.N
THROUGH = [list(map(int, H.through[p])) for p in range(N)]
LOG = os.path.join(HERE, 'search_log.jsonl')
STALL = 60


def colouring(seed):
    """q+1 perfect matchings points->lines partitioning all flags (each step removes one matching)."""
    rng = random.Random(seed)
    rem = [list(t) for t in THROUGH]
    classes = []
    for _ in range(Q + 1):
        m = perfect_matching(N, rem, rng)
        classes.append(m)
        for p in range(N):
            rem[p].remove(m[p])
    seen = {(p, m[p]) for m in classes for p in range(N)}
    assert len(seen) == (Q + 1) * N
    assert seen == {(p, L) for p in range(N) for L in THROUGH[p]}
    return classes


def hops(seed):
    rng = random.Random(seed * 7919 + 1)
    s1 = list(range(N))
    rng.shuffle(s1)
    s2 = list(range(N))
    rng.shuffle(s2)
    return s1, s2


def base_text(k, classes, v, W1, W2, s1, s2, cls):
    out = []
    for c in range(Q + 1):
        m = classes[c]
        vc = v[c] % k
        for p in range(N):
            out.append(f'{p} {N + m[p]} 0 {vc}')
    for p in range(N):
        c = cls[p]
        out.append(f'{p} {N + s1[p]} 1 {W1[c] % k}')
        out.append(f'{p} {N + s2[p]} 2 {W2[c] % k}')
    return f'{2 * N} {M1} {k} {len(out)}\n' + '\n'.join(out) + '\n'


def unreached(text, step, D=8):
    r = subprocess.run(['timeout', '900', 'nice', '-n', '10', LIFTDIAM, '-', str(D), '1', str(step)],
                       input=text, capture_output=True, text=True)
    if 'unreached_pairs' not in r.stdout:
        raise RuntimeError(r.stdout + r.stderr)
    return int(r.stdout.split('unreached_pairs')[1].split()[0])


class Inst:
    def __init__(self, k, seed, mcls):
        self.k = k
        self.mcls = mcls
        self.classes = colouring(seed)
        self.s1, self.s2 = hops(seed)
        rng = random.Random(seed * 104729 + 3)
        self.cls = [0] * N if mcls == 1 else [rng.randrange(mcls) for _ in range(N)]

    def score(self, st, step):
        v, W1, W2 = st
        return unreached(base_text(self.k, self.classes, v, W1, W2, self.s1, self.s2, self.cls), step)


def random_state(inst, rng):
    v = [0] + [rng.randrange(inst.k) for _ in range(Q)]
    W1 = [rng.randrange(inst.k) for _ in range(inst.mcls)]
    W2 = [rng.randrange(inst.k) for _ in range(inst.mcls)]
    return (v, W1, W2)


def neighbour(inst, st, rng):
    v, W1, W2 = [list(x) for x in st]
    slots = [('v', c) for c in range(1, Q + 1)] + [('W1', c) for c in range(inst.mcls)] + \
            [('W2', c) for c in range(inst.mcls)]
    kind, c = rng.choice(slots)
    arr = {'v': v, 'W1': W1, 'W2': W2}[kind]
    arr[c] = rng.choice([x for x in range(inst.k) if x != arr[c]])
    return (v, W1, W2)


def climb(inst, st, cur, step, rng, t_end):
    evals = 0
    while cur > 0 and time.time() < t_end:
        nst = neighbour(inst, st, rng)
        new = inst.score(nst, step)
        evals += 1
        if new <= cur:
            st, cur = nst, new
    return st, cur, evals


def search(inst, budget, step, rng):
    """random restarts + hill-climb (accept <=) at the screen step; stops at the first 0."""
    t_end = time.time() + budget
    best = None
    evals = 0
    while time.time() < t_end and (best is None or best[0] > 0):
        st = random_state(inst, rng)
        cur = inst.score(st, step)
        evals += 1
        stall = 0
        while cur > 0 and time.time() < t_end and stall < STALL:
            nst = neighbour(inst, st, rng)
            new = inst.score(nst, step)
            evals += 1
            if new <= cur:
                stall = 0 if new < cur else stall + 1
                st, cur = nst, new
            else:
                stall += 1
        if best is None or cur < best[0]:
            best = (cur, st)
    return best, evals


def log(rec):
    with open(LOG, 'a') as fh:
        fh.write(json.dumps(rec) + '\n')
    print(json.dumps(rec), flush=True)


def main():
    k = int(sys.argv[1])
    mode = sys.argv[2]
    seeds = [int(x) for x in sys.argv[3].split(',')]
    budget = float(sys.argv[4])
    step = int(sys.argv[5])
    mcls = {'const': 1, 'cls2': 2, 'cls3': 3}[mode]
    M = M1 * k
    for seed in seeds:
        t0 = time.time()
        inst = Inst(k, seed, mcls)
        rng = random.Random(seed * 31 + k)
        (cur, st), evals = search(inst, budget, step, rng)
        rec = {'M': M, 'k': k, 'mode': mode, 'seed': seed, 'screen_step': step, 'screen_unreached': cur,
               'v': st[0], 'W1': st[1], 'W2': st[2], 'evals': evals}
        if cur == 0:
            rec['exact_unreached'] = inst.score(st, 1)
        rec['secs'] = round(time.time() - t0, 1)
        log(rec)


if __name__ == '__main__':
    main()
