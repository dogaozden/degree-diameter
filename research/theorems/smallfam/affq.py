"""Exhaustive Haar-graph scan over G = F_q x| C_k (q = p^e a prime power, C_k acting through r = g^((q-1)/k0), k0 | k),
the subgroups of AGL(1,q) extended by a central cyclic part when k0 < k.  For e = 1 this is frob_scan.py's family.

Element (a, j), a in F_q (integer 0..q-1 = coefficient vector base p), j in Z_k, index a*k + j;
(a,j)(b,l) = (a + r^j b, j + l).  Normal form (same proof as for p prime: conjugation by a translation, scaling by
F_q^*): S = {(0,0), (0,j1), (1,j2), s3, ...} with r^j1 != 1.  The table is written for hx (tab mode) together with the
quotient map to Z_k (hx QMAP filter).

Usage: python3 affq.py DELTA D NMIN NMAX [--emin 2] [--threads 4] [--maxsets 4e7]
"""
import argparse
import itertools
import os
import subprocess
from math import comb, gcd

HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad')


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def prime_powers(lo, hi, emin):
    out = []
    for p in range(2, hi + 1):
        if not is_prime(p):
            continue
        q, e = p, 1
        while q <= hi:
            if e >= emin and q >= lo:
                out.append((q, p, e))
            q *= p
            e += 1
    return sorted(out)


class GF:
    def __init__(self, p, e):
        self.p, self.e, self.q = p, e, p ** e
        # irreducible monic f of degree e with a primitive root x (search)
        for coeffs in itertools.product(range(p), repeat=e):
            f = list(coeffs) + [1]           # f = x^e + c_{e-1} x^{e-1} + ... + c_0
            if f[0] == 0:
                continue
            exp, log = self._try(f)
            if exp is not None:
                self.f, self.exp, self.log = f, exp, log
                return
        raise ValueError('no primitive polynomial')

    def _try(self, f):
        p, e, q = self.p, self.e, self.p ** self.e
        # powers of x mod f, as integer codes
        cur = [1] + [0] * (e - 1)
        exp = []
        seen = set()
        for i in range(q - 1):
            code = sum(c * p ** t for t, c in enumerate(cur))
            if code in seen:
                return None, None
            seen.add(code)
            exp.append(code)
            # multiply by x
            nxt = [0] + cur[:-1]
            top = cur[-1]
            nxt = [(nxt[t] - top * f[t]) % p for t in range(e)]
            cur = nxt
        if len(seen) != q - 1:
            return None, None
        log = {c: i for i, c in enumerate(exp)}
        return exp, log

    def add(self, a, b):
        p = self.p
        r, m = 0, 1
        for _ in range(self.e):
            r += ((a % p + b % p) % p) * m
            a //= p
            b //= p
            m *= p
        return r

    def mulpow(self, a, t):
        """a * x^t"""
        if a == 0:
            return 0
        return self.exp[(self.log[a] + t) % (self.q - 1)]


def write_group(F, k, k0, tab, qmap):
    q = F.q
    N = q * k
    step = (q - 1) // k0          # r = x^step has order k0
    # addition table of F_q, and multiplication by r^j as a permutation
    addt = [[F.add(a, b) for b in range(q)] for a in range(q)]
    rj = [[F.mulpow(b, (step * j) % (q - 1)) for b in range(q)] for j in range(k)]
    with open(tab, 'w') as f:
        f.write(f'{N} 0\n')
        for x in range(N):
            a, j = divmod(x, k)
            row = []
            for y in range(N):
                b, l = divmod(y, k)
                row.append(addt[a][rj[j][b]] * k + (j + l) % k)
            f.write(' '.join(map(str, row)) + '\n')
    with open(qmap, 'w') as f:
        f.write(f'{k}\n')
        for x in range(k):
            f.write(' '.join(str((x + y) % k) for y in range(k)) + '\n')
        f.write(' '.join(str(x % k) for x in range(N)) + '\n')
    return step


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--emin', type=int, default=2)
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--maxsets', type=float, default=4e7)
    a = ap.parse_args()
    outdir = os.path.join(HERE, 'runs', f'affq_d{a.Delta}D{a.D}')
    os.makedirs(outdir, exist_ok=True)
    for (q, p, e) in prime_powers(2, a.nmax, a.emin):
        F = None
        for k in range(2, min(a.nmax // q, q) + 1):
            N = q * k
            if N < a.nmin or N > a.nmax:
                continue
            for k0 in range(2, k + 1):
                if k % k0 or (q - 1) % k0:
                    continue
                sets = (k0 - 1) * k * (comb(N - 3, a.Delta - 3) if a.Delta > 3 else 1)
                if sets > a.maxsets:
                    print(f'q={q} k={k} k0={k0} N={N} skip sets={sets:.3g}', flush=True)
                    continue
                if F is None:
                    F = GF(p, e)
                tab = os.path.join(SP, f'affq_tab_{q}_{k}_{k0}.txt')
                qmap = os.path.join(SP, f'affq_qmap_{q}_{k}_{k0}.txt')
                plan = os.path.join(SP, f'affq_plan_{q}_{k}_{k0}.txt')
                step = write_group(F, k, k0, tab, qmap)
                with open(plan, 'w') as f:
                    for j1 in range(1, k):
                        if j1 % k0 == 0:
                            continue
                        for j2 in range(k):
                            f.write(f'{j1} {1 * k + j2}\n')
                env = dict(os.environ, THREADS=str(a.threads), QMAP=qmap)
                out = subprocess.run([os.path.join(HERE, 'hx'), 'tab', tab, str(a.Delta), str(a.D), plan, '5'],
                                     capture_output=True, text=True, env=env).stdout
                sols = [l for l in out.splitlines() if l.startswith('SOL')]
                dl = [l for l in out.splitlines() if l.startswith('DONE')][0].split()
                print(f'q={q} k={k} k0={k0} N={N} n={2*N} poly={F.f} tested={dl[2]} solutions={dl[4]} best={dl[6]}',
                      flush=True)
                if sols:
                    with open(os.path.join(outdir, f'affq_{q}_{k}_{k0}.txt'), 'w') as f:
                        f.write(f'# Haar graph Delta={a.Delta} D={a.D} G = F_{q} x| C_{k}, r = x^{step} (order {k0}), '
                                f'F_{q} = F_{p}[x]/(f), f coefficients low..high {F.f}; element a*k+j with a the base-{p} '
                                f'code of a field element; N={N} n={2*N}; {dl[4]} normal-form solutions\n')
                        f.write('\n'.join(sols) + '\n')
                for path in (tab, qmap, plan):
                    os.remove(path)


if __name__ == '__main__':
    main()
