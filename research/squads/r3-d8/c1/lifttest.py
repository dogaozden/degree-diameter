#!/usr/bin/env python3
"""Lift test for j=2 hops (card c1, round r3-d8).

usage: lifttest.py Q M1,M2,... SEED1,SEED2,... VARIANT1,VARIANT2,...
  VARIANT = near_holo | near_zero | rand_holo | rand_zero
  near_*: hops = annealed near-dualities c1/s{Q}_h1.txt, c1/s{Q}_h2.txt
  rand_*: hops = random matchings c1/rand{Q}_h1.txt, c1/rand{Q}_h2.txt
  holo: flag voltages uniform in Z_M; zero: all flag voltages 0. Hop voltages uniform in Z_M always.
Writes c1/results_q{Q}.json. Lift files are written to a temp dir and deleted after each liftdiam run.
"""
import json
import os
import random
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SHARED = HERE.parent / 'shared'
LIFTDIAM = Path('/home/user/degree-diameter/research/theorems/d8/liftdiam')
RE_U = re.compile(r'unreached_pairs (\d+)')
RE_MULTI = re.compile(r'multi_edges (\d+)')


def load_gh(q):
    with open(SHARED / f'gh{q}.txt') as fh:
        qq, N = map(int, fh.readline().split())
        lines = [[int(x) for x in fh.readline().split()] for _ in range(N)]
    assert qq == q and all(len(L) == q + 1 for L in lines)
    return N, lines


def read_perm(path, N):
    with open(path) as fh:
        s = [int(x) for x in fh.read().split()]
    assert len(s) == N and sorted(s) == list(range(N)), path
    return s


def check_hops(N, lines, hops):
    """hops must avoid flags, and the two hops must never coincide at a point (no multi-edges)."""
    inc = {(p, k) for k in range(N) for p in lines[k]}
    for s in hops:
        assert all((p, s[p]) not in inc for p in range(N))
    assert all(hops[0][p] != hops[1][p] for p in range(N))


def build_lift(path, N, lines, hops, M, seed, holo):
    rng = random.Random(seed)
    edges = []
    for k in range(N):
        for p in lines[k]:
            a = rng.randrange(M) if holo else 0
            edges.append((p, N + k, a))
    for s in hops:
        for p in range(N):
            edges.append((p, N + s[p], rng.randrange(M)))
    with open(path, 'w') as fh:
        fh.write(f'{2 * N} {M} 1 {len(edges)}\n')
        for u, v, a in edges:
            fh.write(f'{u} {v} {a} 0\n')


def run_diam(path):
    env = dict(os.environ, THREADS='1')
    r = subprocess.run([str(LIFTDIAM), str(path), '8', '1'], capture_output=True, text=True, timeout=900, env=env)
    mu, mm = RE_U.search(r.stdout), RE_MULTI.search(r.stdout)
    if not mu or not mm:
        raise RuntimeError(r.stdout + r.stderr)
    return int(mu.group(1)), int(mm.group(1))


def main():
    q = int(sys.argv[1])
    Ms = [int(x) for x in sys.argv[2].split(',')]
    seeds = [int(x) for x in sys.argv[3].split(',')]
    variants = sys.argv[4].split(',')
    N, lines = load_gh(q)
    hopsets = {
        'near': [read_perm(HERE / f's{q}_h1.txt', N), read_perm(HERE / f's{q}_h2.txt', N)],
        'rand': [read_perm(HERE / f'rand{q}_h1.txt', N), read_perm(HERE / f'rand{q}_h2.txt', N)],
    }
    for name in hopsets:
        check_hops(N, lines, hopsets[name])
    tmp = HERE / 'lifts_tmp'
    tmp.mkdir(exist_ok=True)
    out_path = HERE / f'results_q{q}.json'
    results = []
    for M in Ms:
        for var in variants:
            kind, mode = var.split('_')
            holo = (mode == 'holo')
            Us = []
            for seed in seeds:
                path = tmp / f'q{q}_{var}_M{M}_s{seed}.txt'
                build_lift(path, N, lines, hopsets[kind], M, seed, holo)
                U, multi = run_diam(path)
                path.unlink()
                results.append({'q': q, 'M': M, 'variant': var, 'seed': seed, 'U': U, 'multi_edges': multi})
                Us.append(U)
                if multi != 0:
                    print('WARNING multi_edges', multi, file=sys.stderr)
            print(f'q={q} M={M} {var:10s} U per seed {Us} ok={any(u == 0 for u in Us)}', flush=True)
            with open(out_path, 'w') as fh:
                json.dump(results, fh, indent=1)
    try:
        tmp.rmdir()
    except OSError:
        pass


if __name__ == '__main__':
    main()
