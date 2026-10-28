#!/usr/bin/env python3
"""Label search for LPS(5) x Z_m covers (c4). Labels z0=0, z1=1, z2..z5 searched in Z_m by random restarts + hill climbing.
Objective f = number of vertices (both sides) at distance > T from (I,A) and (I,B), using haar_ecc profiles; FULL required.
Usage: search.py q m T [restarts] [budget] [seed]   prints one line per success or the best failure."""
import subprocess, sys, random, re, os
H = '/home/user/degree-diameter/research/theorems/haar_families'
HAAR = f'{H}/haar_ecc'
def base(q):
    out = subprocess.run(['python3', f'{H}/gen_lps_cover.py', '5', str(q), '1', 'zero'], capture_output=True, text=True).stdout
    return [tuple(map(int, l.split()[:4])) for l in out.strip().splitlines()]
def run(q, m, B, z):
    lines = ''.join(f'{a} {b} {c} {d} {zz}\n' for (a, b, c, d), zz in zip(B, z))
    r = subprocess.run([HAAR, 'pgl', str(q), str(m), '-p'], input=lines, capture_output=True, text=True, timeout=900)
    prof = [list(map(int, l.split(':')[1].split())) for l in r.stdout.splitlines() if l.startswith('profile')]
    mm = re.search(r'compA=(\d+) compB=(\d+)', r.stdout)
    return prof, int(mm.group(1)), int(mm.group(2))
def score(q, m, B, z, T):
    V = q * (q * q - 1) * m
    prof, cA, cB = run(q, m, B, z)
    full = (cA == V and cB == V)
    diam = max(len(p) - 1 for p in prof)
    beyond = sum(sum(p[T + 1:]) for p in prof)
    return (0 if full else 1), beyond, diam, cA
def search(q, m, T, restarts, budget, seed):
    rnd = random.Random(seed)
    B = base(q); V = q * (q * q - 1) * m
    best = None
    for rs in range(restarts):
        z = [0, 1] + [rnd.randrange(m) for _ in range(4)]
        nf, f, d, cA = score(q, m, B, z, T)
        cur = (nf, f)
        for it in range(budget):
            if cur == (0, 0): break
            zn = list(z); i = rnd.choice([2, 3, 4, 5])
            zn[i] = rnd.randrange(m) if rnd.random() < 0.5 else (zn[i] + rnd.choice([-1, 1, -2, 2, m // 2 or 1])) % m
            nf2, f2, d2, cA2 = score(q, m, B, zn, T)
            if (nf2, f2) <= cur: z, cur, d, cA = zn, (nf2, f2), d2, cA2
        if best is None or cur < best[0]: best = (cur, z, d)
        if cur == (0, 0):
            return {'q': q, 'm': m, 'T': T, 'V': V, 'ok': True, 'labels': z, 'diam': d, 'restart': rs}
    return {'q': q, 'm': m, 'T': T, 'V': V, 'ok': False, 'best_f': best[0], 'labels': best[1], 'diam': best[2]}
if __name__ == '__main__':
    q, m, T = map(int, sys.argv[1:4])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    budget = int(sys.argv[5]) if len(sys.argv) > 5 else 60
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    print(search(q, m, T, restarts, budget, seed), flush=True)
