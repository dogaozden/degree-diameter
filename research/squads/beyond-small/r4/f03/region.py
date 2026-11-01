#!/usr/bin/env python3
"""f03 (round 4, side A): region destroy-and-regrow over Z22-orbit packings of side A (swapped graph Gswap).
A region is a set of keys (j, y) (key = j*256 + y, j = controller index blk//22, y = fibre id): either one F4-line
{y0 + l*c} or one F4-plane {y0 + a*c1 + b*c2} for a fixed j. Every orbit whose base uses a key of the region is dropped,
growb regrows for SECS seconds from the rest, the result is kept if it has at least as many orbits.
usage: region.py SECS TOTAL_SECS
"""
import os, random, subprocess, sys, time
F = os.path.dirname(os.path.abspath(__file__))
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/Gswap.edges'
GROWB = os.path.join(F, 'growb')
H = 16896
SECS = int(sys.argv[1]); TOTAL = float(sys.argv[2])
MUL4 = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]

def scal(l, a):
    r = 0
    for k in range(4): r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k)
    return r

def lead(c):
    for k in range(4):
        if (c >> (2 * k)) & 3: return (c >> (2 * k)) & 3
    return -1

DIRS = [c for c in range(1, 256) if lead(c) == 1]   # 85 fibre direction classes
def key(t): return (t >> 8) // 22 * 256 + (t & 255)

def load(p):
    with open(p) as f: return [list(map(int, l.split())) for l in f if l.strip()]

def write(p, orbs):
    with open(p, 'w') as f:
        for o in orbs: f.write(' '.join(map(str, o)) + '\n')

def main():
    best = load(os.path.join(F, 'start_swap.txt'))
    print('start', len(best), flush=True)
    t0 = time.time(); log = open(os.path.join(F, 'region.log'), 'a')
    it = 0; acc = 0
    while time.time() - t0 < TOTAL:
        it += 1
        j = random.randrange(3); c1 = random.choice(DIRS); y0 = random.randrange(256)
        if random.random() < 0.7:
            span = {scal(l, c1) for l in range(4)}; kind = 'line'
        else:
            c2 = random.choice(DIRS)
            span = {scal(a, c1) ^ scal(b, c2) for a in range(4) for b in range(4)}
            if len(span) < 16: continue
            kind = 'plane'
        R = {j * 256 + (y0 ^ s) for s in span}
        keep = [o for o in best if not any(key(v) in R for v in o)]
        ndrop = len(best) - len(keep)
        fix = os.path.join(F, 'fix.txt'); tryf = os.path.join(F, 'try.txt')
        write(fix, keep)
        if os.path.exists(tryf): os.remove(tryf)
        seed = random.randrange(1, 10**9)
        try:
            subprocess.run([GROWB, EDGES, fix, tryf, str(SECS), str(seed), '6', '4000'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=SECS + 200)
            new = load(tryf) if os.path.exists(tryf) else []
        except Exception as e:
            new = []; print('error', e, flush=True)
        ok = len(new) >= len(best) and len(new) >= len(keep)
        if ok:
            acc += 1
            if len(new) > len(best):
                for old in os.listdir(F):
                    if old.startswith('best_sideA_') and old.endswith('.txt'): os.remove(os.path.join(F, old))
                write(os.path.join(F, 'best_sideA_%d.txt' % len(new)), [[v + H for v in o] for o in new])
            best = new
        msg = '%d %s j=%d drop=%d keep=%d regrow=%d best=%d %s t=%.0f' % (
            it, kind, j, ndrop, len(keep), len(new), len(best), 'ACC' if ok else 'rej', time.time() - t0)
        print(msg, flush=True); log.write(msg + '\n'); log.flush()
    print('done', it, 'iterations, accepted', acc, 'final', len(best), flush=True)

if __name__ == '__main__':
    main()
