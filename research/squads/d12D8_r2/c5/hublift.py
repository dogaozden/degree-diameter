#!/usr/bin/env python3
"""hublift.py: twisted hub lift of the H(q) incidence graph (card c5, squad d12D8 r2).

Base graph B = incidence graph of H(q): n points (base ids 0..n-1) and n lines (base ids n..2n-1), degree q+1.
Copies: vertex (b, x) of the lift has id b*c + x, x in Z_c.
Voltage lift: base edge e = (p, n+l) with voltage g_e gives edges (p, x) -- (n+l, (x + g_e) mod c) for all x.
Hubs: h = 2m base hubs per base vertex, m = c // k, k = |S|. Hub (b, j) has id 2n*c + b*h + j and class r = j // 2;
its neighbourhood is S_j = {x : x mod m == r} (size k). Each class is used twice, so every copy x lies in exactly
two hub sets of b, and copy degree is (q+1) + 2 = 6, hub degree k. (Check: 2c = h*k.)

Usage:
  hublift.py --q 3 --c 6 --k 6 --volt zero|random|file [--seed S] [--volt-file F] [--save-volt F] --out EDGES
  hublift.py ... --search ITERS [--nsample 400] --out EDGES      (runs hlsearch local search first)
Output: first line = number of vertices, then one "a b" edge per line (0-based), as apsp/eccs expect.
"""
import sys, os, argparse, random, subprocess

TOOLS = '/home/user/degree-diameter/research/d12D8/tools'
sys.path.insert(0, TOOLS)
from hexlib import load_hex  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
HLSEARCH = os.path.join(HERE, 'hlsearch')


def base_edges(q):
    """Return (n, edges) with edges[e] = (point, n+line), e = line*(q+1) + position."""
    n, lines = load_hex(q)
    edges = []
    for l in range(n):
        for pos in range(q + 1):
            edges.append((int(lines[l][pos]), n + l))
    return n, edges


def write_base(q, path):
    n, edges = base_edges(q)
    with open(path, 'w') as f:
        f.write(f"{2 * n} {len(edges)}\n")
        for p, L in edges:
            f.write(f"{p} {L}\n")
    return n, edges


def hub_params(c, k):
    assert c % k == 0, 'need k | c'
    m = c // k
    return m, 2 * m  # m classes, h = 2m hubs per base vertex (h*k = 2c)


def lift_edges(q, c, k, volt):
    n, edges = base_edges(q)
    NB = 2 * n
    m, h = hub_params(c, k)
    assert len(volt) == len(edges)
    out = []
    for e, (p, L) in enumerate(edges):
        g = volt[e] % c
        for x in range(c):
            out.append((p * c + x, L * c + (x + g) % c))
    hub_base = NB * c
    for b in range(NB):
        for j in range(h):
            hub = hub_base + b * h + j
            r = j // 2
            for x in range(r, c, m):
                out.append((b * c + x, hub))
    N = NB * c + NB * h
    return N, out


def write_edges(N, out, path):
    with open(path, 'w') as f:
        f.write(f"{N}\n")
        for a, b in out:
            f.write(f"{a} {b}\n")


def check_degrees(N, out):
    deg = [0] * N
    for a, b in out:
        deg[a] += 1
        deg[b] += 1
    return max(deg), min(deg)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--q', type=int, default=3)
    ap.add_argument('--c', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--volt', choices=['zero', 'random', 'file'], default='random')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--volt-file')
    ap.add_argument('--save-volt')
    ap.add_argument('--search', type=int, default=0, help='local-search iterations (hlsearch)')
    ap.add_argument('--nsample', type=int, default=400)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()

    n, edges = base_edges(a.q)
    E = len(edges)
    rng = random.Random(a.seed)
    if a.volt == 'zero':
        volt = [0] * E
    elif a.volt == 'random':
        volt = [rng.randrange(a.c) for _ in range(E)]
    else:
        volt = [int(x) for x in open(a.volt_file).read().split()]
        assert len(volt) == E, (len(volt), E)

    if a.search:
        base = os.path.join(os.path.dirname(os.path.abspath(a.out)), f'base_q{a.q}.txt')
        write_base(a.q, base)
        vin = os.path.join(os.path.dirname(os.path.abspath(a.out)), f'volt_in_{a.c}_{a.k}_{a.seed}.txt')
        with open(vin, 'w') as f:
            f.write('\n'.join(map(str, volt)) + '\n')
        vout = a.save_volt or (a.out + '.volt')
        cmd = [HLSEARCH, base, str(a.c), str(hub_params(a.c, a.k)[0]), str(a.search), str(a.seed),
               str(a.nsample), vin, vout]
        print('running', ' '.join(cmd), flush=True)
        subprocess.run(cmd, check=True)
        volt = [int(x) for x in open(vout).read().split()]

    if a.save_volt and not a.search:
        with open(a.save_volt, 'w') as f:
            f.write('\n'.join(map(str, volt)) + '\n')

    N, out = lift_edges(a.q, a.c, a.k, volt)
    write_edges(N, out, a.out)
    mx, mn = check_degrees(N, out)
    m, h = hub_params(a.c, a.k)
    print(f"wrote {a.out}: vertices={N} (=728*({a.c}+{h})={2*n*(a.c+h)}) edges={len(out)} "
          f"maxdeg={mx} mindeg={mn} m={m} h={h}")


if __name__ == '__main__':
    main()
