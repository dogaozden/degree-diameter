#!/usr/bin/env python3
"""levscan.py (card c4, squad r2_d14D8): systematic scan of level skeletons for lifts of H(q) + 2 extra edges.

Generalizes cells/d14D8_work/opus/mk_lev.py. Lift group Z_L x Z_k, CRT to cyclic Z_m with m = L*k, gcd(L,k) = 1.
Hexagon flags: level 0, random sub-voltage in Z_k. Extra edge j (j = 1, 2): level s_j in Z_L, sub-voltage random per
point, along one of the phi-modes:
  same  : one random bijection phi, used by both extra edges (phi doubled)
  indep : two independent random bijections
  digon : extra edge 1 along a perfect matching of the flags (parallel to a hexagon flag), extra edge 2 along phi
Pairs (s1, s2) are taken up to multiplication by the units of Z_L (one representative per orbit; the hexagon level
is fixed at 0, so no translation). A design with a repeated (point, line, voltage) triple is rejected.

Subcommands:
  screen  --q 5 --L 3,4,... --seeds 2 --tsv T --log G    every structure, downward k-scan, exact check (lscan all)
  confirm --q 7 --structs L:s1:s2:phi;...  --seeds 2 --tsv T --log G   r:200 sampling, then exact check (lscan all)
  gen     --q Q --L L --k k --s1 s1 --s2 s2 --phi P --seed S --out FILE  one base file (hexagon flags first)
Run with `python3 -B` (no bytecode written into the shared tool folder).
"""
import argparse
import os
import subprocess
import sys
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LSCAN = os.path.join(HERE, 'lscan')
TOOLS = '/home/user/degree-diameter/research/squads/cells/d14D8_work'
sys.path.insert(0, TOOLS)
from hexlib import load, hex_edges  # shared read-only tool

PHIMODES = ('same', 'indep', 'digon')
_H, _M = {}, {}


def H(q):
    if q not in _H:
        _H[q] = load(q)
    return _H[q]


def crt_table(L, k):
    """T[a, b] = x in Z_{Lk} with x = a mod L and x = b mod k."""
    T = np.zeros((L, k), dtype=np.int64)
    for x in range(L * k):
        T[x % L, x % k] = x
    return T


def flag_matching(q, seed=12345):
    """Perfect matching of the incidence graph: point p -> line M[p] through p (greedy + augmenting paths)."""
    if q in _M:
        return _M[q]
    N, LP, PL, coord = H(q)
    rng = np.random.default_rng(seed)
    adj = [rng.permutation(PL[p]).tolist() for p in range(N)]
    mp, ml = [-1] * N, [-1] * N
    for p in rng.permutation(N).tolist():
        for l in adj[p]:
            if ml[l] < 0:
                ml[l], mp[p] = p, l
                break
    for p0 in rng.permutation(N).tolist():
        if mp[p0] >= 0:
            continue
        parent = {p0: None}
        queue, qi, found = [p0], 0, None
        while qi < len(queue) and found is None:
            p = queue[qi]
            qi += 1
            for l in adj[p]:
                if ml[l] < 0:
                    found = (p, l)
                    break
                pp = ml[l]
                if pp not in parent:
                    parent[pp] = (p, l)
                    queue.append(pp)
        if found is None:
            raise RuntimeError('no perfect matching of the flags')
        p, l = found
        while True:
            mp[p], ml[l] = l, p
            pr = parent[p]
            if pr is None:
                break
            p, l = pr
    assert len(set(mp)) == N
    _M[q] = np.array(mp, dtype=np.int64)
    return _M[q]


def build(q, L, k, s1, s2, phimode, seed):
    """Return (N, m, E) with E rows (point, line, voltage), hexagon flags first, or None if a triple repeats."""
    m = L * k
    assert gcd(L, k) == 1 and phimode in PHIMODES
    N, LP, PL, coord = H(q)
    T = crt_table(L, k)
    rng = np.random.default_rng(seed)
    hv = rng.integers(0, k, LP.shape) if k > 1 else np.zeros(LP.shape, dtype=np.int64)
    parts = [hex_edges(LP, T[0, hv])]
    phi = rng.permutation(N)
    if phimode == 'same':
        maps = [phi, phi]
    elif phimode == 'indep':
        maps = [phi, rng.permutation(N)]
    else:
        maps = [flag_matching(q), phi]
    for s, ph in zip((s1, s2), maps):
        c = rng.integers(0, k, N) if k > 1 else np.zeros(N, dtype=np.int64)
        parts.append(np.stack([np.arange(N), ph, T[s % L, c]], axis=1))
    E = np.concatenate(parts).astype(np.int64)
    key = (E[:, 0] * N + E[:, 1]) * m + E[:, 2]
    if len(np.unique(key)) != len(key):
        return None
    return N, m, E


def to_text(N, m, E):
    return f'{N} {N} {m}\n' + '\n'.join(f'{a} {b} {v}' for a, b, v in E.tolist()) + '\n'


def lscan(text, D, spec, early):
    env = dict(os.environ, EARLY='1' if early else '0')
    r = subprocess.run([LSCAN, '-', str(D), spec], input=text, capture_output=True, text=True, env=env, timeout=1500)
    return r.returncode == 0, r.stdout.strip()


def unit_reps(L):
    """One representative (s1 <= s2) per orbit of unordered pairs in Z_L under multiplication by units."""
    units = [u for u in range(1, L) if gcd(u, L) == 1]
    seen, reps = set(), []
    for s1 in range(L):
        for s2 in range(s1, L):
            if (s1, s2) in seen:
                continue
            orb = {tuple(sorted(((u * s1) % L, (u * s2) % L))) for u in units} | {(s1, s2)}
            seen |= orb
            reps.append((s1, s2))
    return reps


def k_list(L, mcap=64):
    return [k for k in range(1, mcap // L + 1) if gcd(k, L) == 1]


def scan_struct(q, L, s1, s2, phimode, seeds, spec, early, logf, mcap=64):
    """Downward k-scan (largest m first). Returns (m, k, seed, output) of the first design that passes, or None."""
    for k in reversed(k_list(L, mcap)):
        for seed in range(seeds):
            b = build(q, L, k, s1, s2, phimode, seed)
            if b is None:
                logf.write(f'q{q} L{L} s{s1},{s2} {phimode} k{k} seed{seed} DUP\n')
                continue
            N, m, E = b
            ok, out = lscan(to_text(N, m, E), 8, spec, early)
            logf.write(f'q{q} L{L} s{s1},{s2} {phimode} k{k} m{m} seed{seed} spec={spec} '
                       f'{"PASS" if ok else "FAIL"} {out}\n')
            logf.flush()
            if ok:
                return m, k, seed, out
    return None


def cmd_screen(a):
    logf = open(a.log, 'a')
    tsv = open(a.tsv, 'a')
    for L in [int(x) for x in a.L.split(',')]:
        for s1, s2 in unit_reps(L):
            for pm in PHIMODES:
                res = scan_struct(a.q, L, s1, s2, pm, a.seeds, 'all', True, logf)
                if res:
                    m, k, seed, out = res
                    line = f'{L}\t{s1}\t{s2}\t{pm}\t{m}\t{k}\t{seed}\tPASS\n'
                else:
                    line = f'{L}\t{s1}\t{s2}\t{pm}\tnull\tnull\tnull\tFAIL\n'
                tsv.write(line)
                tsv.flush()
                print(line.rstrip(), flush=True)


def cmd_confirm(a):
    logf = open(a.log, 'a')
    tsv = open(a.tsv, 'a')
    for item in a.structs.split(';'):
        L, s1, s2, pm = item.split(':')
        L, s1, s2 = int(L), int(s1), int(s2)
        res = None
        for k in reversed(k_list(L)):
            for seed in range(a.seeds):
                b = build(a.q, L, k, s1, s2, pm, seed)
                if b is None:
                    continue
                N, m, E = b
                text = to_text(N, m, E)
                ok, out = lscan(text, 8, 'r:200:7', True)
                logf.write(f'q{a.q} L{L} s{s1},{s2} {pm} k{k} m{m} seed{seed} r:200 {"PASS" if ok else "FAIL"} {out}\n')
                logf.flush()
                if not ok:
                    continue
                ok2, out2 = lscan(text, 8, 'all', True)
                logf.write(f'q{a.q} L{L} s{s1},{s2} {pm} k{k} m{m} seed{seed} all {"PASS" if ok2 else "FAIL"} {out2}\n')
                logf.flush()
                if ok2:
                    res = (m, k, seed)
                    break
            if res:
                break
        line = f'{L}\t{s1}\t{s2}\t{pm}\t' + ('\t'.join(map(str, res)) + '\tPASS' if res else 'null\tnull\tnull\tFAIL') + '\n'
        tsv.write(line)
        tsv.flush()
        print(line.rstrip(), flush=True)


def cmd_gen(a):
    b = build(a.q, a.L, a.k, a.s1, a.s2, a.phi, a.seed)
    if b is None:
        sys.exit('repeated (point, line, voltage) triple: pick another seed')
    N, m, E = b
    with open(a.out, 'w') as f:
        f.write(to_text(N, m, E))
    print(f'wrote {a.out}: N={N} m={m} edges={len(E)}')


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    s = sub.add_parser('screen')
    s.add_argument('--q', type=int, default=5)
    s.add_argument('--L', default='3,4,5,6,7,8,9')
    s.add_argument('--seeds', type=int, default=2)
    s.add_argument('--tsv', required=True)
    s.add_argument('--log', required=True)
    c = sub.add_parser('confirm')
    c.add_argument('--q', type=int, default=7)
    c.add_argument('--structs', required=True)
    c.add_argument('--seeds', type=int, default=2)
    c.add_argument('--tsv', required=True)
    c.add_argument('--log', required=True)
    g = sub.add_parser('gen')
    g.add_argument('--q', type=int, required=True)
    g.add_argument('--L', type=int, required=True)
    g.add_argument('--k', type=int, required=True)
    g.add_argument('--s1', type=int, required=True)
    g.add_argument('--s2', type=int, required=True)
    g.add_argument('--phi', choices=PHIMODES, required=True)
    g.add_argument('--seed', type=int, required=True)
    g.add_argument('--out', required=True)
    a = ap.parse_args()
    {'screen': cmd_screen, 'confirm': cmd_confirm, 'gen': cmd_gen}[a.cmd](a)


if __name__ == '__main__':
    main()
