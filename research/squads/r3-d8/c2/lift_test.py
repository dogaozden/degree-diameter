#!/usr/bin/env python3
"""Card c2: Z_5 x Z_K lifts of the incidence graph of H(q) plus two hop matchings, scored by liftdiam at D = 8.

Base graph: points 0..N-1, lines N..2N-1; flag f = k*G+j joins point lines_pts[k*G+j] to line N+k (G = q+1).
Voltages (Z_5 part first): flags (0, vol[f]); hop 1 (1, h1[p]) on the edge p -- N+hop1[p]; hop 2 (2, h2[p]).
Hop matchings: random perfect matchings points -> lines that avoid flags and each other.

usage: lift_test.py q K VOL_FILE|random SEEDS(comma list) [out.json]
  VOL_FILE: one Z_K voltage per flag (holo output).  'random' draws fresh uniform Z_K flag voltages per seed.
"""
import json
import random
import subprocess
import sys
import os

ROOT = '/home/user/degree-diameter/research/squads/r3-d8'
LIFTDIAM = '/home/user/degree-diameter/research/theorems/d8/liftdiam'
HERE = os.path.dirname(os.path.abspath(__file__))


def load_gh(q):
    with open(f'{ROOT}/shared/gh{q}.txt') as fh:
        qq, N = map(int, fh.readline().split())
        assert qq == q, (qq, q)
        lines = [list(map(int, fh.readline().split())) for _ in range(N)]
    return N, lines


def hop_matchings(N, lines, rng):
    inc = [set() for _ in range(N)]
    for k, pts in enumerate(lines):
        for p in pts:
            inc[p].add(k)
    while True:
        hops = []
        ok = True
        for h in range(2):
            m = [-1] * N
            avail = list(range(N))
            order = list(range(N))
            rng.shuffle(order)
            for p in order:
                forb = inc[p] if h == 0 else (inc[p] | {hops[0][p]})
                pick = None
                for _ in range(200):
                    i = rng.randrange(len(avail))
                    if avail[i] not in forb:
                        pick = i
                        break
                if pick is None:
                    idx = [i for i, c in enumerate(avail) if c not in forb]
                    if not idx:
                        ok = False
                        break
                    pick = rng.choice(idx)
                m[p] = avail[pick]
                avail[pick] = avail[-1]
                avail.pop()
            if not ok:
                break
            hops.append(m)
        if ok:
            return hops


def write_lift(path, N, lines, G, K, vol, hops, labels):
    E = N * G + 2 * N
    with open(path, 'w') as fh:
        fh.write(f'{2 * N} 5 {K} {E}\n')
        for k, pts in enumerate(lines):
            for j, p in enumerate(pts):
                fh.write(f'{p} {N + k} 0 {vol[k * G + j]}\n')
        for h in range(2):
            for p in range(N):
                fh.write(f'{p} {N + hops[h][p]} {h + 1} {labels[h][p]}\n')


def run_liftdiam(path, D=8):
    res = subprocess.run(['timeout', '900', 'nice', '-n', '10', LIFTDIAM, path, str(D), '1'],
                         capture_output=True, text=True)
    out = res.stdout.splitlines()
    header = out[0]
    U = maxecc = None
    for line in out:
        if line.startswith('D '):
            parts = line.split()
            U = int(parts[parts.index('unreached_pairs') + 1])
            maxecc = parts[parts.index('max_ecc') + 1]
    multi = int(header.split('multi_edges')[1].split()[0])
    bip = int(header.split('bipartite')[1].split()[0])
    return dict(U=U, max_ecc=maxecc, multi_edges=multi, bipartite=bip, header=header)


def main():
    q = int(sys.argv[1])
    K = int(sys.argv[2])
    volarg = sys.argv[3]
    seeds = [int(s) for s in sys.argv[4].split(',')]
    outjson = sys.argv[5] if len(sys.argv) > 5 else f'{HERE}/lift_q{q}_K{K}.json'
    N, lines = load_gh(q)
    G = q + 1
    F = N * G
    vol_design = None
    if volarg != 'random':
        with open(volarg) as fh:
            vol_design = [int(x) for x in fh.read().split()]
        assert len(vol_design) == F, (len(vol_design), F)
    os.makedirs(f'{HERE}/lifts', exist_ok=True)
    rows = []
    for s in seeds:
        hop_rng = random.Random(1000003 * s + 17 * q + K)
        hops = hop_matchings(N, lines, hop_rng)
        labels = [[hop_rng.randrange(K) for _ in range(N)] for _ in range(2)]
        # random Z_K flag voltages paired with this hop seed (comparison arm)
        frng = random.Random(7919 * s + 31 * q + K)
        vol_rand = [frng.randrange(K) for _ in range(F)]
        arms = {'random': vol_rand}
        if vol_design is not None:
            arms = {'designed': vol_design, 'random': vol_rand}
        for arm, vol in arms.items():
            path = f'{HERE}/lifts/lift_q{q}_K{K}_{arm}_s{s}.txt'
            write_lift(path, N, lines, G, K, vol, hops, labels)
            r = run_liftdiam(path)
            row = dict(q=q, K=K, M=5 * K, arm=arm, seed=s, **r)
            rows.append(row)
            print(json.dumps({k: v for k, v in row.items() if k != 'header'}), flush=True)
            os.remove(path)
    with open(outjson, 'w') as fh:
        json.dump(rows, fh, indent=1)


if __name__ == '__main__':
    main()
