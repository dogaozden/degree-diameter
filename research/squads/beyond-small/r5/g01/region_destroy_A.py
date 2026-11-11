#!/usr/bin/env python3
"""r5 g01: region destroy on side A (swapped graph Gswap, ids < 16896 = A-side bases in swapped form).
Adapted from r4/f07/region_destroy.py. Keys of a base N are (j, y) = divmod(((t>>8)//22)*256 + (t&255), 256).
Each round: pick a region R of keys (affine fibre lines in a random direction c), drop every orbit whose keys meet R,
regrow with growb, keep if the orbit count is >= the current count. Improvements are saved in GLOBAL ids (+16896).
usage: region_destroy_A.py SECS_PER_GROW TOTAL_SECS SEED"""
import random, subprocess, sys, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/Gswap.edges'
GROWB = os.path.join(HERE, 'growb')
H = 16896
MUL4 = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def scal(l, a):
    r = 0
    for k in range(4): r |= MUL4[l][(a >> (2*k)) & 3] << (2*k)
    return r
DIRS = []
for c in range(1, 256):
    lead = next((((c >> (2*k)) & 3) for k in range(4) if (c >> (2*k)) & 3), 0)
    if lead == 1: DIRS.append(c)
def key(t): return ((t >> 8) // 22) * 256 + (t & 255)
def load(fn):
    out = []
    for l in open(fn):
        if l.strip(): out.append([int(x) for x in l.split()])
    return out
def keys_of(N): return {key(t) for t in N}
def count_ok(N_list):
    ks = set()
    for N in N_list:
        k = [key(t) for t in N]
        if len(set(k)) != len(k) or ks & set(k): return False
        ks |= set(k)
    return True
def write(fn, orbs, shift=0):
    with open(fn, 'w') as f:
        for N in orbs: f.write(' '.join(str(t + shift) for t in N) + '\n')
def region(rng):
    c = rng.choice(DIRS)
    mode = rng.choice(['all_j', 'all_j', 'one_j2', 'one_j1'])
    nl = 1 if mode == 'all_j' else 2
    R = set()
    js = [0, 1, 2] if mode == 'all_j' else [rng.randrange(3)]
    for _ in range(nl):
        y0 = rng.randrange(256)
        L = [y0 ^ scal(l, c) for l in range(4)]
        for j in js:
            for y in L: R.add(j * 256 + y)
    return mode, c, R
def main():
    secs = float(sys.argv[1]); total = float(sys.argv[2]); seed = int(sys.argv[3])
    rng = random.Random(seed)
    best = load(os.path.join(HERE, 'bestA_swap.txt'))
    assert count_ok(best), 'start file not key-disjoint'
    cur_n = len(best)
    log = open(os.path.join(HERE, 'rd_log.txt'), 'a')
    t0 = time.time(); it = 0
    while time.time() - t0 < total:
        it += 1
        tries = 0
        while True:
            tries += 1
            mode, c, R = region(rng)
            drop = [i for i, N in enumerate(best) if keys_of(N) & R]
            if 2 <= len(drop) <= 9 or tries > 200: break
        if not (2 <= len(drop) <= 9): drop = drop[:9]
        dset = set(drop)
        fix = [N for i, N in enumerate(best) if i not in dset]
        fixfn = os.path.join(HERE, 'fix_A.txt'); outfn = os.path.join(HERE, 'try_A.txt')
        write(fixfn, fix)
        if os.path.exists(outfn): os.remove(outfn)
        s = rng.randrange(1, 10**7)
        t1 = time.time()
        subprocess.run(['nice', '-n', '10', GROWB, EDGES, fixfn, outfn, str(int(secs)), str(s), '6', '4000'],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        new = load(outfn) if os.path.exists(outfn) else []
        ok = len(new) >= len(fix) and count_ok(new)
        acc = ok and len(new) >= cur_n
        if acc:
            if len(new) > cur_n: write(os.path.join(HERE, f'best_sideA_{len(new)}.txt'), new, shift=H)
            best = new; cur_n = len(new)
            write(os.path.join(HERE, 'bestA_swap.txt'), best)
        msg = f"it {it} t={time.time()-t0:.0f}s mode={mode} c={c} |R|={len(R)} dropped={len(drop)} fixed={len(fix)} new_total={len(new)} ok={ok} accepted={acc} cur={cur_n} dt={time.time()-t1:.0f}s"
        print(msg, flush=True); log.write(msg + '\n'); log.flush()
    log.close()
if __name__ == '__main__': main()
