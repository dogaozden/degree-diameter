#!/usr/bin/env python3
"""g12 (round 5, side B): adaptive mix of four destroy-and-repair styles on side B.
Styles: region (affine key region drop, growb 45 s), big (drop 8-12, 2 growb seeds of 40 s, keep best),
conflict (blk scores, drop 2-4 most blocking orbits, growb 60 s), small (drop 3-6 random, growb 90 s).
Style choice: round-robin for the first 4 iterations, then random with weight = recent reward rate + 0.1 over the last
8 outcomes of that style. Reward: 1 strict improvement, 0.5 accepted with the same count, 0 otherwise.
Every accepted state is key-disjoint and has >= the start orbit count. Seeds from base 13000.
usage: mix.py TOTAL_SECS"""
import random, subprocess, sys, time, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
GROWB = os.path.join(HERE, 'growb'); BLK = os.path.join(HERE, 'blk')
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
    return [[int(x) for x in l.split()] for l in open(fn) if l.strip()]
def keys_of(N): return {key(t) for t in N}
def count_ok(L):
    ks = set()
    for N in L:
        k = [key(t) for t in N]
        if len(set(k)) != len(k) or ks & set(k): return False
        ks |= set(k)
    return True
def write(fn, orbs):
    with open(fn, 'w') as f:
        for N in orbs: f.write(' '.join(map(str, N)) + '\n')
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
def grow(fix, secs, seed, R=6, tag='t'):
    fixfn = os.path.join(HERE, f'fix_{tag}.txt'); outfn = os.path.join(HERE, f'try_{tag}.txt')
    write(fixfn, fix)
    if os.path.exists(outfn): os.remove(outfn)
    subprocess.run(['nice', '-n', '10', GROWB, EDGES, fixfn, outfn, str(int(secs)), str(seed), '6', str(R)],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=secs + 60)
    return load(outfn) if os.path.exists(outfn) else []

def step_region(rng, best, seed):
    for tries in range(1, 201):
        mode, c, R = region(rng)
        drop = [i for i, N in enumerate(best) if keys_of(N) & R]
        if 2 <= len(drop) <= 9: break
    drop = drop[:9]
    fix = [N for i, N in enumerate(best) if i not in set(drop)]
    new = grow(fix, 45, seed, 6, 'B')
    return fix, new, f"mode={mode} c={c} |R|={len(R)} dropped={len(drop)}"

def step_big(rng, best, seed):
    R = rng.randrange(8, 13)
    idx = set(rng.sample(range(len(best)), R))
    fix = [N for i, N in enumerate(best) if i not in idx]
    bestnew = []
    for s in (seed, seed + 1):
        new = grow(fix, 40, s, 6, 'B')
        if len(new) > len(bestnew) and count_ok(new): bestnew = new
    return fix, bestnew, f"dropped={R}"

def step_conflict(rng, best, seed):
    n = len(best)
    write(os.path.join(HERE, 'cur_B.txt'), best)
    subprocess.run(['nice', '-n', '10', BLK, EDGES, os.path.join(HERE, 'cur_B.txt'), os.path.join(HERE, 'score_cur.txt'),
                    '0', str(seed), '6', '400'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=160)
    sc = []
    try:
        for l in open(os.path.join(HERE, 'score_cur.txt')):
            p = l.split()
            if len(p) >= 2: sc.append((float(p[1]) + rng.random() * 0.5, int(p[0])))
    except FileNotFoundError:
        sc = []
    if len(sc) < n:  # fall back to random drop
        drop = set(rng.sample(range(n), rng.randrange(2, 5)))
    else:
        sc.sort(reverse=True)
        drop = {i for _, i in sc[:rng.randrange(2, 5)]}
    fix = [N for i, N in enumerate(best) if i not in drop]
    new = grow(fix, 60, seed, 4000, 'B')
    return fix, new, f"drop={sorted(drop)}"

def step_small(rng, best, seed):
    R = rng.randrange(3, 7)
    idx = set(rng.sample(range(len(best)), R))
    fix = [N for i, N in enumerate(best) if i not in idx]
    new = grow(fix, 90, seed, 8000, 'B')
    return fix, new, f"dropped={R}"

STYLES = {'region': step_region, 'big': step_big, 'conflict': step_conflict, 'small': step_small}

def main():
    total = float(sys.argv[1])
    rng = random.Random(13000)
    best = load(os.path.join(HERE, 'startB.txt'))
    assert count_ok(best), 'start not key-disjoint'
    cur_n = len(best)
    hist = collections.defaultdict(lambda: collections.deque(maxlen=8))
    log = open(os.path.join(HERE, 'mix_log.txt'), 'a')
    t0 = time.time(); it = 0; names = list(STYLES)
    while time.time() - t0 < total:
        it += 1
        if it <= len(names):
            style = names[it - 1]
        else:
            w = [(sum(hist[s]) / len(hist[s]) if hist[s] else 0.25) + 0.1 for s in names]
            style = rng.choices(names, weights=w)[0]
        seed = 13000 + it * 11 + rng.randrange(10)
        t1 = time.time()
        fix, new, info = STYLES[style](rng, best, seed)
        ok = len(new) >= len(fix) and count_ok(new)
        n_new = len(new)
        if ok and n_new >= cur_n:
            r = 1.0 if n_new > cur_n else 0.5
            if n_new > cur_n:
                write(os.path.join(HERE, f'best_sideB_{n_new}.txt'), new)
                write(os.path.join(HERE, 'bestB.txt'), new)
            best = new; cur_n = n_new; acc = True
        else:
            r = 0.0; acc = False
        hist[style].append(r)
        msg = (f"it {it} t={time.time()-t0:.0f}s style={style} {info} seed={seed} fixed={len(fix)} "
               f"new={n_new} ok={ok} accepted={acc} cur={cur_n} reward={r} dt={time.time()-t1:.0f}s")
        print(msg, flush=True); log.write(msg + '\n'); log.flush()
    log.write(f"DONE best {cur_n}\n"); log.close()
    print('DONE', cur_n, flush=True)
if __name__ == '__main__': main()
