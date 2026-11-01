#!/usr/bin/env python3
"""haarsweep.py D Nlo Nhi klo khi [maxlam]: exhaustive sweep of cubic Haar graphs of metacyclic groups Z_n x|_lambda Z_k
(n prime, lambda^k = 1, lambda != 1) through liftsym EXH: H(Z_n x| Z_k, {e, (x1,a), (x2,b)}) is the symmetric Z_n lift
of the base Haar(Z_k, {0,a,b}) with rho = rotation; after gauge fixing one orbit voltage is free and is scaled to 1,
so each (k, {0,a,b}, n, lambda) is ONE graph (plus degenerate ones). j-patterns up to the maps a -> u a and
{0,a,b} -> {0,b-a,-a} (translation) are tried once. Prints solutions (FOUND) and a per-group summary."""
import sys, subprocess, os, math
D, Nlo, Nhi, klo, khi = map(int, sys.argv[1:6]); maxlam = int(sys.argv[6]) if len(sys.argv) > 6 else 99
here = os.path.dirname(os.path.abspath(__file__)); os.makedirs(f'{here}/hs', exist_ok=True)
def isprime(x): return x > 1 and all(x % p for p in range(2, int(x**.5) + 1))
best = {}
for k in range(klo, khi + 1):
    units = [u for u in range(1, k) if math.gcd(u, k) == 1]
    pats, seen = [], set()
    for a in range(1, k):
        for b in range(a + 1, k):
            if math.gcd(math.gcd(a, b), k) != 1: continue            # base must be connected
            cls = set()
            for u in units:
                for (x, y) in ((a, b), (b - a, (-a) % k), ((-b) % k, (a - b) % k)):
                    p = tuple(sorted(((u * x) % k, (u * y) % k)))
                    cls.add(p)
            if any(c in seen for c in cls): continue
            seen |= cls; pats.append((a, b))
    for (a, b) in pats:
        base = f'{here}/hs/h{k}_{a}_{b}'
        with open(base + '.txt', 'w') as f:
            f.write(f'{2*k}\n')
            for i in range(k):
                for s in (0, a, b): f.write(f'{i} {k + (i + s) % k}\n')
        with open(base + '.perm', 'w') as f: f.write(' '.join(str((i + 1) % k) for i in range(k)) + ' ' + ' '.join(str(k + (i + 1) % k) for i in range(k)) + '\n')
        for n in range(max(3, Nlo // k), Nhi // k + 1):
            if not isprime(n) or (n - 1) % k and math.gcd(n - 1, k) == 1: continue
            lams = [l for l in range(2, n) if pow(l, k, n) == 1][:maxlam]
            for l in lams:
                tag = f'{base}_n{n}_l{l}'
                r = subprocess.run([f'{here}/../bin/liftsym', base + '.txt', base + '.perm', str(n), str(l), str(D), '1', '1', tag],
                                   env=dict(os.environ, EXH='1'), capture_output=True, text=True)
                line = [x for x in r.stdout.split('\n') if x.startswith('EXHRESULT')]
                if not line: continue
                mc = int(line[0].split('min_cost=')[1].split()[0])
                if mc == 0:
                    print('FOUND', k, a, b, n, l, 2 * k * n, line[0].split('solutions=')[1].split()[0], flush=True)
                else:
                    for ext in ('.best', '.edges'):
                        try: os.remove(tag + ext)
                        except FileNotFoundError: pass
print('done', file=sys.stderr)
