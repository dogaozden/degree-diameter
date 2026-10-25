"""Haar-graph screen over products A x B of two Frobenius-type groups (the shape of Loz's (4,8) group (C7:C3) x Dic13).

A factor is F_q x|_lam C_a: elements (x, i), x in F_q, i in Z_a, (x, i)(y, j) = (x + lam^i y, i + j), where lam in
F_q^* has order t > 1 dividing a (t < a: a central cyclic part, e.g. Dic13 = F_13 x| C_4 with t = 2).  One lam per
order t (other generators of <lam> give isomorphic groups).  q runs over prime powers (F_q built from a primitive
polynomial).  The product's multiplication table is built with numpy and annealed with hanneal (hx.c 'tab' format).
Usage: SCRATCH=dir python3 frobprod.py DELTA D NMIN NMAX [--secs 10] [--seeds 1] [--qmax 200] [--list]
       --skip-library: skip orders that GAP's SmallGroups library covers (those are in fscreen.py's runs)
Output: <OUTDIR or runs>/frobprod_d{DELTA}D{D}.tsv: N A B costs best_set
"""
import argparse
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp')


def prime_powers(qmax):
    out = []
    for q in range(2, qmax + 1):
        p = next(d for d in range(2, q + 1) if q % d == 0)
        e, x = 0, q
        while x % p == 0:
            x //= p; e += 1
        if x == 1:
            out.append((q, p, e))
    return out


def gf(q, p, e):
    """Additive group F_p^e as integers 0..q-1 (base-p digits); returns (add table, mul table) as numpy arrays."""
    digits = np.array([[(x // p ** k) % p for k in range(e)] for x in range(q)], dtype=np.int64)
    pw = np.array([p ** k for k in range(e)], dtype=np.int64)
    add = ((digits[:, None, :] + digits[None, :, :]) % p) @ pw
    if e == 1:
        mul = np.outer(np.arange(q), np.arange(q)) % p
        return add, mul
    # find a monic irreducible (primitive) polynomial of degree e by brute force
    import itertools
    def polymulmod(a, b, f):
        r = [0] * (2 * e - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
        for d in range(2 * e - 2, e - 1, -1):      # reduce by monic f (f[e] = 1)
            c = r[d]
            if c:
                for k in range(e + 1):
                    r[d - e + k] = (r[d - e + k] - c * f[k]) % p
        return r[:e]
    for tail in itertools.product(range(p), repeat=e):
        f = list(tail) + [1]
        if f[0] == 0:
            continue
        # check x has multiplicative order q-1
        x = [0, 1] + [0] * (e - 2)
        y, o = x[:], 1
        one = [1] + [0] * (e - 1)
        while y != one and o <= q:
            y = polymulmod(y, x, f); o += 1
        if o == q - 1:
            break
    mul = np.zeros((q, q), dtype=np.int64)
    for a in range(q):
        da = list(digits[a])
        for b in range(q):
            mul[a, b] = int(np.dot(polymulmod(da, list(digits[b]), f), pw))
    return add, mul


def factors(qmax, nmax):
    """Frobenius-type factors F_q x| C_a (lam of order t > 1, t | q-1, t | a), order q*a <= nmax."""
    out = []
    for (q, p, e) in prime_powers(qmax):
        for t in range(2, q):
            if (q - 1) % t:
                continue
            a = t
            while q * a <= nmax:
                out.append((q, p, e, t, a))
                a += t
    return out


def factor_table(q, p, e, t, a, cache={}):
    """Multiplication of F_q x| C_a with lam of order t: returns (n, mul function on index arrays)."""
    if (q, p, e) not in cache:
        cache[(q, p, e)] = gf(q, p, e)
    add, mul = cache[(q, p, e)]
    # a generator of F_q^*: find g of order q-1, lam = g^((q-1)/t)
    for g in range(2, q) if q > 2 else []:
        x, o = g, 1
        while x != 1 and o < q:
            x = mul[x, g]; o += 1
        if o == q - 1:
            break
    lam = 1
    for _ in range((q - 1) // t):
        lam = mul[lam, g]
    lpow = [1]
    for _ in range(a - 1):
        lpow.append(mul[lpow[-1], lam])
    lpow = np.array(lpow, dtype=np.int64)
    n = q * a
    idx = np.arange(n)
    X, I = idx // a, idx % a
    # T[u, v] = u * v for u = (X[u], I[u]), v = (X[v], I[v])
    T = add[X[:, None], mul[lpow[I][:, None], X[None, :]]] * a + (I[:, None] + I[None, :]) % a
    return n, T


def name(f):
    q, p, e, t, a = f
    return f'F{q}x|C{a}' + (f'(t{t})' if t != a else '')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--secs', type=float, default=10)
    ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--qmax', type=int, default=200)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--skip-library', action='store_true')
    ap.add_argument('--maxindex', type=int, default=10**9, help='only factors with (q-1)/t <= this (index of <lam> in F_q^*)')
    ap.add_argument('--maxcentral', type=int, default=10**9, help='only factors with a/t <= this (size of the central part)')
    a = ap.parse_args()
    fs = [f for f in factors(a.qmax, a.nmax) if (f[0] - 1) // f[3] <= a.maxindex and f[4] // f[3] <= a.maxcentral]
    cands = []
    for i1 in range(len(fs)):
        for i2 in range(i1, len(fs)):
            n = fs[i1][0] * fs[i1][4] * fs[i2][0] * fs[i2][4]
            if a.nmin <= n <= a.nmax:
                cands.append((n, fs[i1], fs[i2]))
    cands.sort()
    if a.skip_library:
        orders = sorted({c[0] for c in cands})
        script = 'for n in [' + ','.join(map(str, orders)) + '] do Print(n, " ", SmallGroupsAvailable(n), "\\n"); od; QUIT;\n'
        out = subprocess.run(['gap', '-q'], input=script, capture_output=True, text=True).stdout
        lib = {int(l.split()[0]) for l in out.splitlines() if l.strip().endswith('true')}
        cands = [c for c in cands if c[0] not in lib]
    if a.list:
        for n, f1, f2 in cands:
            print(n, name(f1), name(f2))
        print(len(cands), 'candidates')
        return
    outp = os.path.join(os.environ.get('OUTDIR', os.path.join(HERE, 'runs')), f'frobprod_d{a.Delta}D{a.D}.tsv')
    done = set()
    if os.path.exists(outp):
        done = {(l.split('\t')[1], l.split('\t')[2]) for l in open(outp) if l[0].isdigit()}
    log = open(outp, 'a')
    for n, f1, f2 in cands:
        if (name(f1), name(f2)) in done:
            continue
        n1, T1 = factor_table(*f1)
        n2, T2 = factor_table(*f2)
        # product index u = u1 * n2 + u2
        tab = os.path.join(SP, f'fp_{n}_{os.getpid()}.txt')
        with open(tab, 'w') as fh:
            fh.write(f'{n} 0\n')
            for u1 in range(n1):
                for u2 in range(n2):
                    row = (T1[u1][:, None] * n2 + T2[u2][None, :]).reshape(-1)
                    fh.write(' '.join(map(str, row.tolist())) + '\n')
        costs, bset = [], '-'
        for s in range(1, a.seeds + 1):
            out = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(a.Delta), str(a.D), str(a.secs), str(s), '8',
                                  os.path.join(SP, f'fp_sol_{n}_{s}.txt')], capture_output=True, text=True).stdout
            res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
            best = int(res[4].split('=')[1])
            if not costs or best < min(costs):
                bset = ' '.join(res[res.index('best_set') + 1:])
            costs.append(best)
            if best == 0:
                print(f'*** {n} {name(f1)} x {name(f2)}: cost 0, S = {bset}', flush=True)
                break
        log.write(f'{n}\t{name(f1)}\t{name(f2)}\t{",".join(map(str, costs))}\t{bset}\n')
        log.flush()
        os.remove(tab)


if __name__ == '__main__':
    main()
