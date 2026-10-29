#!/usr/bin/env python3
"""Three-level (7,7) graph: levels 0,1,2 of H(q); transitions i -> i+1 (mod 3) all with the same sigma and freed set R;
line-side hub t ~ (R[t], 0),(R[t],1),(R[t],2); point-side hub s ~ (sigma(R[s]), 0..2); hub graph edges (t, s).
Vertex ids: point (p,i) -> 2N*i + p ; line (l,i) -> 2N*i + N + l ; line-side hub t -> 6N + t ; point-side hub s -> 6N + Hn + s.
usage (as module): build(q, N, LP, sig, R, hubedges, Hn, HP) -> (n, edge list)
usage (CLI): build3.py SOL OUT.edges [--add-free P ...] [--hub FILE]   (SOL = record-format file, or hub FILE overrides)"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load

HEX = '/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q5.bin'


def read_sol(fn):
    lines = open(fn).read().split('\n')
    hdr = lines[0].split()
    assert hdr[0] == 'multi'
    q, N, r, m, Hn, HP, n = map(int, hdr[1:8])
    R = [int(t) for t in lines[1].split()[1:]]
    hk = lines[2].split(); k = int(hk[1])
    hub = [(int(hk[2 + 2 * i]), int(hk[3 + 2 * i])) for i in range(k)]
    sig = [int(t) for s in lines[3:] for t in s.split()]
    return q, N, R, hub, Hn, HP, np.array(sig, np.int64)


def build(q, N, LP, sig, R, hub, Hn, HP):
    E = []
    for i in range(3):
        base = 2 * N * i
        for l in range(N):
            for p in LP[l]:
                E.append((base + int(p), base + N + l))
    freed = np.zeros(N, bool); freed[list(R)] = True
    for i in range(3):
        base = 2 * N * i; nxt = 2 * N * ((i + 1) % 3)
        for p in range(N):
            if not freed[p]:
                E.append((base + p, nxt + N + int(sig[p])))
    B = 6 * N
    for t in range(Hn):
        x = R[t]
        for i in range(3):
            E.append((B + t, 2 * N * i + x))
    for s in range(HP):
        x = R[s]
        for i in range(3):
            E.append((B + Hn + s, 2 * N * i + N + int(sig[x])))
    for a, b in hub:
        E.append((B + a, B + Hn + b))
    n = B + Hn + HP
    return n, np.array(E, np.int64)


def write_edges(fn, n, E):
    with open(fn, 'w') as f:
        f.write(f'{n}\n')
        np.savetxt(f, E, fmt='%d')


if __name__ == '__main__':
    sol, out = sys.argv[1], sys.argv[2]
    q, N, LP, PL, X = load(HEX)
    q2, N2, R, hub, Hn, HP, sig = read_sol(sol)
    assert N2 == N and len(sig) == N
    n, E = build(q, N, LP, sig, R, hub, Hn, HP)
    write_edges(out, n, E)
    print(f'n={n} edges={len(E)} |R|={len(R)} K={Hn} HP={HP}')
