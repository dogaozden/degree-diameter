#!/usr/bin/env python3
"""g06 (round 5, side A): adaptive mix of four destroy-and-regrow styles on the side-swapped graph.

State is kept in swapped ids (Gswap.edges); saved best files are converted to global ids (+16896).
Styles (chosen per iteration with probability proportional to (reward+1)/(uses+2)):
  region   - region destroy (r4/f07): drop orbits meeting a random affine key region, regrow 45 s
  big      - big destroy (r4/f08): drop 8-12 random orbits, two growb seeds of 38 s, keep the best
  conflict - conflict-directed destroy (r4/f06): blk scores, drop the 2-4 most blocking orbits, regrow 60 s
  small    - small destroy with a long repair (r4/f05): drop 3-6 random orbits, regrow 90 s with R=8000
Accept if the regrown packing is valid and has at least as many orbits as the current one.
usage: mix.py TIMEBOX_SECS
"""
import random, subprocess, time, os, sys, json

HERE = os.path.dirname(os.path.abspath(__file__))
G = '/home/user/degree-diameter/research/squads/beyond-small/data/Gswap.edges'
GROWB = os.path.join(HERE, 'growb')
BLK = os.path.join(HERE, 'blk')
OFF = 16896
MUL4 = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
DIRS = []
for c in range(1, 256):
    lead = next((((c >> (2 * k)) & 3) for k in range(4) if (c >> (2 * k)) & 3), 0)
    if lead == 1:
        DIRS.append(c)


def scal(l, a):
    r = 0
    for k in range(4):
        r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k)
    return r


def key(t):
    return ((t >> 8) // 22) * 256 + (t & 255)


def keys_of(N):
    return {key(t) for t in N}


def load(fn):
    out = []
    if os.path.exists(fn):
        for l in open(fn):
            if l.strip():
                out.append([int(x) for x in l.split()])
    return out


def write(fn, orbs):
    with open(fn, 'w') as f:
        for N in orbs:
            f.write(' '.join(map(str, N)) + '\n')


def count_ok(orbs):
    ks = set()
    for N in orbs:
        k = [key(t) for t in N]
        if len(set(k)) != len(k) or ks & set(k):
            return False
        ks |= set(k)
    return True


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
            for y in L:
                R.add(j * 256 + y)
    return mode, c, R


def growb(fixed, secs, seed, tag, R=4000, KD=6):
    fx = os.path.join(HERE, f'fix_{tag}.txt')
    out = os.path.join(HERE, f'try_{tag}.txt')
    write(fx, fixed)
    if os.path.exists(out):
        os.remove(out)
    subprocess.run(['nice', '-n', '10', 'timeout', str(int(secs) + 60), GROWB, G, fx, out,
                    str(int(secs)), str(seed), str(KD), str(R)],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return load(out)


def blk_scores(cur, seed, tag):
    fx = os.path.join(HERE, f'fix_{tag}.txt')
    sc = os.path.join(HERE, 'score_cur.txt')
    write(fx, cur)
    subprocess.run(['nice', '-n', '10', 'timeout', '400', BLK, G, fx, sc, '0', str(seed), '6', '1000'],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    s = {}
    if os.path.exists(sc):
        for l in open(sc):
            p = l.split()
            if len(p) >= 2:
                s[int(p[0])] = int(p[1])
    return s


def main():
    timebox = float(sys.argv[1]) if len(sys.argv) > 1 else 2900
    rng = random.Random(7000)
    cur = load(os.path.join(HERE, 'cur.txt'))
    assert count_ok(cur), 'start packing not key-disjoint'
    best_n = len(cur)
    styles = ['region', 'big', 'conflict', 'small']
    uses = {s: 0 for s in styles}
    reward = {s: 0.0 for s in styles}
    log = open(os.path.join(HERE, 'log.jsonl'), 'a')
    t0 = time.time()
    it = 0
    while time.time() - t0 < timebox:
        it += 1
        # style choice: round-robin for the first four, then proportional to a smoothed success rate
        if it <= len(styles):
            st = styles[it - 1]
        else:
            w = {s: (reward[s] + 1.0) / (uses[s] + 2.0) for s in styles}
            tot = sum(w.values())
            x = rng.random() * tot
            acc_w = 0.0
            st = styles[-1]
            for s in styles:
                acc_w += w[s]
                if x <= acc_w:
                    st = s
                    break
        uses[st] += 1
        seed = 7000 + rng.randrange(1, 10 ** 6)
        n_old = len(cur)
        t1 = time.time()
        info = {}
        new = None
        if st == 'region':
            tries = 0
            while True:
                tries += 1
                mode, c, R = region(rng)
                drop = [i for i, N in enumerate(cur) if keys_of(N) & R]
                if 2 <= len(drop) <= 9 or tries > 200:
                    break
            if not (2 <= len(drop) <= 9):
                drop = rng.sample(range(len(cur)), 3)
            fixed = [N for i, N in enumerate(cur) if i not in set(drop)]
            new = growb(fixed, 45, seed, 'g06')
            info = {'mode': mode, 'c': c, '|R|': len(R), 'drop': len(drop)}
        elif st == 'big':
            R_ = rng.randint(8, 12)
            drop = set(rng.sample(range(len(cur)), R_))
            fixed = [N for i, N in enumerate(cur) if i not in drop]
            best = []
            for k in range(2):
                cand = growb(fixed, 38, seed + k, f'g06b{k}')
                if len(cand) > len(best):
                    best = cand
            new = best
            info = {'drop': R_}
        elif st == 'conflict':
            sc = blk_scores(cur, seed % 100000 + 1, 'g06blk')
            K = rng.randint(2, 4)
            ranked = sorted(range(len(cur)), key=lambda k: -(sc.get(k, 0) + rng.random() * 0.5))
            drop = set(ranked[:K])
            fixed = [N for i, N in enumerate(cur) if i not in drop]
            new = growb(fixed, 60, seed, 'g06c')
            info = {'drop': K, 'drop_idx': sorted(drop), 'sc1_max': max(sc.values()) if sc else -1}
        else:  # small
            R_ = rng.randint(3, 6)
            drop = set(rng.sample(range(len(cur)), R_))
            fixed = [N for i, N in enumerate(cur) if i not in drop]
            new = growb(fixed, 90, seed, 'g06s', R=8000)
            info = {'drop': R_}
        ok = len(new) >= len(fixed) and count_ok(new)
        acc = bool(ok and len(new) >= n_old)
        improved = acc and len(new) > best_n
        if acc:
            cur = new
            write(os.path.join(HERE, 'cur.txt'), cur)
        if improved:
            best_n = len(cur)
            write(os.path.join(HERE, f'best_swap_{best_n}.txt'), cur)
            write(os.path.join(HERE, f'best_sideA_{best_n}.txt'), [[t + OFF for t in N] for N in cur])
        # reward: 1 for a new best, 0.3 for an accepted equal-size move, 0 otherwise
        reward[st] += 1.0 if improved else (0.3 if (acc and len(cur) == n_old) else 0.0)
        rec = {'it': it, 't': round(time.time() - t0), 'style': st, 'seed': seed, 'old': n_old,
               'new': len(new), 'valid': ok, 'accepted': acc, 'cur': len(cur), 'best': best_n,
               'dt': round(time.time() - t1), **info}
        log.write(json.dumps(rec) + '\n')
        log.flush()
    log.write(json.dumps({'done': True, 'best': best_n, 'uses': uses, 'reward': reward}) + '\n')
    log.close()


if __name__ == '__main__':
    main()
