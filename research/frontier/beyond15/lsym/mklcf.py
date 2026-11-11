#!/usr/bin/env python3
"""mklcf.py NAME "a1,a2,...,ap" REPS [SHIFT]: LCF graph [a1..ap]^REPS (Hamiltonian cycle 0..N-1 plus chords i ~ i+a_(i mod p)),
written in the lift format (first line N, then "u v"), relabelled so even cycle positions are 0..N/2-1 and odd ones
N/2..N-1 (needs all a_i odd: bipartite). Also writes NAME.perm: the automorphism i -> i + SHIFT (default p, the LCF period;
SHIFT must be an even multiple-compatible shift: a multiple of p, even). Prints N, girth, order of the shift."""
import sys, collections
name, lcf, reps = sys.argv[1], [int(x) for x in sys.argv[2].split(',')], int(sys.argv[3])
p = len(lcf); N = p * reps; shift = int(sys.argv[4]) if len(sys.argv) > 4 else p
assert all(a % 2 for a in lcf) and N % 2 == 0 and shift % 2 == 0 and shift % p == 0
E = set()
for i in range(N):
    E.add(tuple(sorted((i, (i + 1) % N)))); E.add(tuple(sorted((i, (i + lcf[i % p]) % N))))
adj = collections.defaultdict(set)
for u, v in E: adj[u].add(v); adj[v].add(u)
assert all(len(adj[v]) == 3 for v in range(N)), "not cubic (repeated chord?)"
lab = lambda i: i // 2 if i % 2 == 0 else N // 2 + i // 2
def girth():
    g = 10**9
    for s in range(N):
        dist = {s: 0}; par = {s: -1}; q = [s]
        for x in q:
            for y in adj[x]:
                if y not in dist: dist[y] = dist[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y: g = min(g, dist[x] + dist[y] + 1)
    return g
with open(name + '.txt', 'w') as f:
    f.write(f'{N}\n')
    for u, v in sorted(E):
        a, b = lab(u), lab(v)
        f.write(f'{min(a,b)} {max(a,b)}\n')
perm = [0] * N
for i in range(N): perm[lab(i)] = lab((i + shift) % N)
with open(name + '.perm', 'w') as f: f.write(' '.join(map(str, perm)) + '\n')
k = N // __import__('math').gcd(N, shift)
print(f'{name}: N={N} edges={len(E)} girth={girth()} shift={shift} order k={k} vertex orbits={N//k} edge orbits={len(E)//k}')
