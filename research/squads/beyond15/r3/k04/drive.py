#!/usr/bin/env python3
"""k04 driver: Gray-shape quotient Q = "3 3 0-0,0-2,0-2,1-0,1-0,1-1,2-1,2-1,2-2" with Z_k voltages (quotgen logic),
then liftsym ANNEAL runs over (k, pattern, n, lambda). Resumable: results go to results.tsv, jobs already there are skipped.
usage: drive.py PHASE BUDGET_SECS   (PHASE = screen | deep)"""
import sys, os, math, random, subprocess, time, json
HERE = os.path.dirname(os.path.abspath(__file__))
F = '/home/user/degree-diameter/research/frontier'
LIFT = f'{F}/bin/liftsym'
QG = f'{HERE}/qg'; RES = f'{HERE}/results.tsv'
tA, tB = 3, 3
Q = [tuple(map(int, e.split('-'))) for e in "0-0,0-2,0-2,1-0,1-0,1-1,2-1,2-1,2-2".split(',')]
nv = tA + tB
par = list(range(nv))
def f_(x):
    while par[x] != x: par[x] = par[par[x]]; x = par[x]
    return x
tree = []
for i, (a, b) in enumerate(Q):
    ra, rb = f_(a), f_(tA + b)
    if ra != rb: par[ra] = rb; tree.append(i)
free = [i for i in range(len(Q)) if i not in tree]
def isprime(x): return x > 1 and all(x % p for p in range(2, int(x ** .5) + 1))
def patterns(k, count, seed):
    rng = random.Random(seed * 1000 + k)
    units = [u for u in range(1, k) if math.gcd(u, k) == 1]
    tried, out, att = set(), [], 0
    while len(out) < count and att < 20000:
        att += 1
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
        out.append(js)
    return out
def write_base(k, js):
    volt = [0] * len(Q)
    for i, j in zip(free, js): volt[i] = j
    edges = [(a * k + i, tA * k + b * k + (i + x) % k) for (a, b), x in zip(Q, volt) for i in range(k)]
    base = f'{QG}/k{k}_' + '_'.join(map(str, js))
    if not os.path.exists(base + '.txt'):
        with open(base + '.txt', 'w') as fh:
            fh.write(f'{nv*k}\n'); [fh.write(f'{u} {v}\n') for u, v in edges]
        perm = [(v // k) * k + (v % k + 1) % k for v in range(nv * k)]
        with open(base + '.perm', 'w') as fh: fh.write(' '.join(map(str, perm)) + '\n')
    return base
def lambdas(n, k, maxl):
    return [l for l in range(2, n) if math.gcd(l, n) == 1 and pow(l, k, n) == 1][:maxl]
def ncands(k, vlo, nmax):
    """first nmax usable n with N = 6k n >= vlo (prime n need gcd(n-1,k)>1; composite n any)."""
    out = []; n = max(3, -(-vlo // (nv * k)))
    while len(out) < nmax and n < vlo + 10**6:
        ok = (isprime(n) and math.gcd(n - 1, k) > 1) or (not isprime(n) and lambdas(n, k, 1))
        if ok: out.append(n)
        n += 1
    return out
def done_set():
    s = set()
    if os.path.exists(RES):
        for line in open(RES):
            p = line.split('\t')
            if len(p) >= 8: s.add((p[0], p[1], p[2], p[3]))
    return s
def run_job(D, k, js, n, l, secs):
    base = write_base(k, js)
    tag = f'{QG}/t_D{D}_k{k}_{"_".join(map(str, js))}_n{n}_l{l}'
    env = dict(os.environ, THREADS='1')
    try:
        r = subprocess.run(['timeout', '105', 'nice', '-n', '10', LIFT, base + '.txt', base + '.perm', str(n), str(l), str(D),
                            str(secs), '1', tag], env=env, capture_output=True, text=True, timeout=110)
        line = [x for x in r.stdout.split('\n') if x.startswith('RESULT')]
    except Exception as e:
        line = []
    if not line: return None
    best = int(line[0].split('best=')[1].split()[0]); N = nv * k * n
    res_edges = None
    if best == 0:
        res_edges = tag + '.edges'
    else:
        for ext in ('.best',):
            try: os.remove(tag + ext)
            except FileNotFoundError: pass
    return best, N, tag, res_edges
def main():
    phase, budget = sys.argv[1], float(sys.argv[2])
    t0 = time.time()
    os.makedirs(QG, exist_ok=True)
    if phase == 'screen':
        jobs = []
        for D, vlo in ((16, 20467), (15, 11791)):
            for k in (5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16):
                for js in patterns(k, 2, seed=D):
                    for n in ncands(k, vlo, 2):
                        ls = lambdas(n, k, 1)
                        for l in ls: jobs.append((D, k, js, n, l, 6))
    else:  # deep: read screen results, take best (lowest cost) per (D,k) and re-anneal longer at larger n
        jobs = json.load(open(f'{HERE}/deep_jobs.json'))
        jobs = [(j[0], j[1], j[2], j[3], j[4], j[5]) for j in jobs]
    dn = done_set()
    for (D, k, js, n, l, secs) in jobs:
        key = (str(D), str(k), '_'.join(map(str, js)), f'{n}:{l}')
        if key in dn: continue
        if time.time() - t0 > budget: break
        out = run_job(D, k, js, n, l, secs)
        if out is None: continue
        best, N, tag, ed = out
        with open(RES, 'a') as fh:
            fh.write('\t'.join([str(D), str(k), '_'.join(map(str, js)), f'{n}:{l}', str(N), str(secs), str(best), tag]) + '\n')
        if best == 0: print('FOUND', D, k, js, n, l, N, ed, flush=True)
    print('batch done', round(time.time() - t0), 's', flush=True)
if __name__ == "__main__": main()
