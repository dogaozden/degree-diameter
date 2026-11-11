#!/usr/bin/env python3
"""quotsweep.py D Nlo Nhi klo khi [maxpat] [seed]: exhaustive search of cubic graphs with a semiregular metacyclic group
Z_n x|_lambda Z_k having 4 vertex orbits (two per side). The quotient by the group is the cubic bipartite multigraph Q4:
a1-b1, a1-b2 (x2), a2-b1 (x2), a2-b2. Z_k voltages on Q4 (spanning tree a1-b1, a1-b2, a2-b1 set to 0; the other three
edges carry j1, j2, j3) give a connected cubic bipartite Z_k-cover B (4k vertices) with the rotation rho of order k;
liftsym EXH then searches every Z_n x|_lambda Z_k symmetric lift of B (2 free orbit voltages, one scaled to 1).
Patterns are reduced by the units of Z_k; at most maxpat patterns per k (random order with the seed) if given.
The Desargues graph is the k = 5 instance used earlier. Prints FOUND lines (2N = 4 k n)."""
import sys, subprocess, os, math, random
D, Nlo, Nhi, klo, khi = map(int, sys.argv[1:6]); maxpat = int(sys.argv[6]) if len(sys.argv) > 6 else 10**9
rng = random.Random(int(sys.argv[7]) if len(sys.argv) > 7 else 1)
here = os.path.dirname(os.path.abspath(__file__)); os.makedirs(f'{here}/qs', exist_ok=True)
def isprime(x): return x > 1 and all(x % p for p in range(2, int(x**.5) + 1))
# Q4 edges: (A-vertex, B-vertex); tree edges first
Q = [(0, 0), (0, 1), (1, 0), (0, 1), (1, 0), (1, 1)]   # a1b1, a1b2, a2b1 (tree), a1b2', a2b1', a2b2
for k in range(klo, khi + 1):
    units = [u for u in range(1, k) if math.gcd(u, k) == 1]
    seen, pats = set(), []
    for j1 in range(k):
        for j2 in range(k):
            for j3 in range(k):
                key = min(tuple((u * j) % k for j in (j1, j2, j3)) for u in units)
                if key in seen: continue
                seen.add(key); pats.append((j1, j2, j3))
    rng.shuffle(pats); pats = pats[:maxpat]
    for (j1, j2, j3) in pats:
        volt = [0, 0, 0, j1, j2, j3]
        # cover B: A side (a, i) -> a*k + i in [0, 2k), B side (b, i) -> 2k + b*k + i
        edges = []
        for (a, b), x in zip(Q, volt):
            for i in range(k): edges.append((a * k + i, 2 * k + b * k + (i + x) % k))
        # connected?
        adj = {}
        for u, v in edges: adj.setdefault(u, []).append(v); adj.setdefault(v, []).append(u)
        seen2 = {0}; st = [0]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen2: seen2.add(y); st.append(y)
        if len(seen2) != 4 * k: continue
        if len(set(tuple(sorted(e)) for e in edges)) != len(edges): continue   # no multi-edges in the cover
        base = f'{here}/qs/q{k}_{j1}_{j2}_{j3}'
        with open(base + '.txt', 'w') as f:
            f.write(f'{4*k}\n'); [f.write(f'{u} {v}\n') for u, v in edges]
        perm = [((v % k) + 1) % k + (v // k) * k for v in range(4 * k)]
        with open(base + '.perm', 'w') as f: f.write(' '.join(map(str, perm)) + '\n')
        for n in range(max(3, Nlo // (4 * k)), Nhi // (4 * k) + 1):
            if not isprime(n) or math.gcd(n - 1, k) == 1: continue
            for l in [l for l in range(2, n) if pow(l, k, n) == 1]:
                tag = f'{base}_n{n}_l{l}'
                r = subprocess.run([f'{here}/../bin/liftsym', base + '.txt', base + '.perm', str(n), str(l), str(D), '1', '1', tag],
                                   env=dict(os.environ, EXH='1'), capture_output=True, text=True)
                line = [x for x in r.stdout.split('\n') if x.startswith('EXHRESULT')]
                if not line: continue
                mc = int(line[0].split('min_cost=')[1].split()[0])
                if mc == 0: print('FOUND', k, j1, j2, j3, n, l, 4 * k * n, flush=True)
                else:
                    for ext in ('.best', '.edges'):
                        try: os.remove(tag + ext)
                        except FileNotFoundError: pass
print('done', file=sys.stderr)
