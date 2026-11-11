"""Simulated annealing over bi-coset graphs of SL(2,64) (see bicoset.py). State = (VA, VB, x).
Cost = number of vertices at distance >= 6 from the two identity cosets (0 means diameter <= 5).
usage: python3 search.py SEED SECONDS OUTPREFIX"""
import json, math, random, sys, time
import bicoset as bc

def valid_subspace(rng):
    while True:
        basis = []
        while len(bc.span(basis)) < 16:
            cand = rng.randrange(1, 64)
            if cand not in bc.span(basis):
                basis.append(cand)
            if len(basis) > 4:
                basis = []
        return basis

def cost_of(VA, VB, x):
    res = bc.run(VA, VB, x)
    if res is None:
        return None
    if res['n_reached'] != 32760 or res['nB_reached'] != 32760 or res['degrees'] != [16]:
        return None
    # run() returns only eccentricities; recompute the number of far vertices cheaply via the histogram-free path
    return res

def far_count(VA, VB, x):
    """number of vertices at distance 6 (or more) from A.1 and from B.1"""
    res = bc.run(VA, VB, x)
    return res

if __name__ == '__main__':
    seed, secs, outp = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed)
    # current state
    while True:
        VA, VB = valid_subspace(rng), valid_subspace(rng)
        x = bc.rand_sl(rng)
        r = bc.run(VA, VB, x)
        if r is not None and r['degrees'] == [16] and r['n_reached'] == 32760:
            break
    cur = (VA, VB, x)
    cur_c = r['ecc_A'] * 1000 + r['ecc_B']  # placeholder, refined below
    # cost = number of far vertices; bc.run only returns ecc, so use the dedicated counter
    def far(state):
        VA, VB, x = state
        return bc.far_counts(VA, VB, x)
    cur_c = far(cur)
    best = (cur_c, cur)
    T0, T1 = 40.0, 2.0
    t0 = time.time()
    steps = 0
    log = open(outp + '.log', 'w')
    while time.time() - t0 < secs:
        steps += 1
        VA, VB, x = cur
        move = rng.random()
        if move < 0.5:
            x2 = bc.rand_sl(rng)
            new = (VA, VB, x2)
        elif move < 0.75:
            new = (valid_subspace(rng), VB, x)
        else:
            new = (VA, valid_subspace(rng), x)
        c = far(new)
        if c is None:
            continue
        frac = (time.time() - t0) / secs
        T = T0 * (T1 / T0) ** frac
        if c <= cur_c or rng.random() < math.exp(-(c - cur_c) / T):
            cur, cur_c = new, c
            if c < best[0]:
                best = (c, new)
                print(json.dumps({'step': steps, 'best_far': c, 'VA': new[0], 'VB': new[1], 'x': new[2]}),
                      file=log, flush=True)
        if best[0] == 0:
            break
    print(json.dumps({'done': True, 'steps': steps, 'best_far': best[0], 'VA': best[1][0], 'VB': best[1][1],
                      'x': best[1][2]}), flush=True)
