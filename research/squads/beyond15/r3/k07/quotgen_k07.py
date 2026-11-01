#!/usr/bin/env python3
"""quotgen.py D Vlo Vhi klo khi QUOT [maxpat] [seed] [maxlam]: exhaustive symmetric lifts over a general quotient.
QUOT: "tA tB a-b,a-b,..." — the cubic bipartite quotient multigraph by the whole group Z_n x| Z_k (tA = tB orbits per
side; each edge joins A-orbit a to B-orbit b). Z_k voltages: 0 on a spanning tree, random patterns on the other edges
(reduced by units of Z_k); the Z_k-cover B (k(tA+tB) vertices, rotation of order k) must be connected and simple;
then liftsym EXH for every prime n with gcd(n-1, k) > 1 and 4.. vertex counts in [Vlo, Vhi], every lambda != 1 with
lambda^k = 1 (up to maxlam). Prints FOUND k pattern n lambda vertices."""
import sys, subprocess, os, math, random
D, Vlo, Vhi, klo, khi = map(int, sys.argv[1:6]); spec = sys.argv[6]
maxpat = int(sys.argv[7]) if len(sys.argv) > 7 else 50; rng = random.Random(int(sys.argv[8]) if len(sys.argv) > 8 else 1)
maxlam = int(sys.argv[9]) if len(sys.argv) > 9 else 99
ASECS = os.environ.get('ANNEAL')   # if set: anneal ASECS seconds per (n, lambda), any n (composite too), no EXH
here = '/home/user/degree-diameter/research/squads/beyond15/r3/k07'; os.makedirs(f'{here}/qg', exist_ok=True)
tA, tB, es = spec.split(' ', 2); tA, tB = int(tA), int(tB)
Q = [tuple(map(int, e.split('-'))) for e in es.split(',')]
# spanning tree of the quotient (union-find over A0..A_{tA-1}, B0..)
par = list(range(tA + tB))
def f(x):
    while par[x] != x: par[x] = par[par[x]]; x = par[x]
    return x
tree = []
for i, (a, b) in enumerate(Q):
    ra, rb = f(a), f(tA + b)
    if ra != rb: par[ra] = rb; tree.append(i)
free = [i for i in range(len(Q)) if i not in tree]
def isprime(x): return x > 1 and all(x % p for p in range(2, int(x**.5) + 1))
tag0 = 'g' + str(abs(hash(spec)) % 10**6)
nv = tA + tB
for k in range(klo, khi + 1):
    units = [u for u in range(1, k) if math.gcd(u, k) == 1]
    tried = set(); pats = 0; attempts = 0
    while pats < maxpat and attempts < 50 * maxpat:
        attempts += 1
        js = [rng.randrange(k) for _ in free]
        key = min(tuple((u * j) % k for j in js) for u in units)
        if key in tried: continue
        tried.add(key)
        volt = [0] * len(Q)
        for i, j in zip(free, js): volt[i] = j
        edges = [(a * k + i, tA * k + b * k + (i + x) % k) for (a, b), x in zip(Q, volt) for i in range(k)]
        if len(set(edges)) != len(edges): continue
        adj = {}
        for u, v in edges: adj.setdefault(u, []).append(v); adj.setdefault(v, []).append(u)
        seen = {0}; st = [0]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen: seen.add(y); st.append(y)
        if len(seen) != nv * k: continue
        pats += 1
        base = f'{here}/qg/{tag0}_k{k}_' + '_'.join(map(str, js))
        with open(base + '.txt', 'w') as fh:
            fh.write(f'{nv*k}\n'); [fh.write(f'{u} {v}\n') for u, v in edges]
        perm = [(v // k) * k + (v % k + 1) % k for v in range(nv * k)]
        with open(base + '.perm', 'w') as fh: fh.write(' '.join(map(str, perm)) + '\n')
        for n in range(max(3, Vlo // (nv * k)), Vhi // (nv * k) + 1):
            if (not ASECS and not isprime(n)) or (isprime(n) and math.gcd(n - 1, k) == 1): continue
            for l in [l for l in range(2, n) if math.gcd(l, n) == 1 and pow(l, k, n) == 1][:maxlam]:
                tag = f'{base}_n{n}_l{l}'
                env = dict(os.environ); secs = ASECS or '1'
                if not ASECS: env['EXH'] = '1'
                r = subprocess.run(['/home/user/degree-diameter/research/frontier/bin/liftsym', base + '.txt', base + '.perm', str(n), str(l), str(D), secs, '1', tag],
                                   env=env, capture_output=True, text=True)
                line = [x for x in r.stdout.split('\n') if x.startswith('EXHRESULT') or x.startswith('RESULT')]
                if not line: continue
                mc = int(line[0].split('min_cost=')[1].split()[0]) if 'min_cost=' in line[0] else int(line[0].split('best=')[1].split()[0])
                print('RUN', k, js, n, l, nv * k * n, 'min_cost', mc, flush=True)
                if mc == 0: print('FOUND', k, js, n, l, nv * k * n, base, flush=True)
                else:
                    for ext in ('.best', '.edges'):
                        try: os.remove(tag + ext)
                        except FileNotFoundError: pass
print('done', file=sys.stderr)
