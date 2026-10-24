"""Exhaustive Haar-graph scan over metacyclic groups Z_p x|_r Z_k with p prime (any k with r^k = 1, faithful or not).

Normal form (proved in SMALL_DEGREE_FAMILIES.md, section 'normal form'): if ord_p(r) = k0 > 1, every connected
H(G,S) is isomorphic to one with S = {(0,0), (0,j1), (1,j2), s3, ..., s_{Delta-1}} where r^{j1} != 1 (conjugation by a
translation kills the a-part of an element whose j-part acts non-trivially; scaling a -> u a sets the next nonzero
a-part to 1; an S with every a-part 0 lies in the subgroup Z_k and is disconnected).  The remaining elements run
over all of G (hx enumerates them).

Usage: python3 frob_scan.py DELTA D NMIN NMAX [--faithful] [--kmin K] [--maxsets M] [--threads T]
Prints one line per group: p k r ord N 2N sets solutions best_cost; writes solutions to runs/frob_D{..}/.
"""
import argparse
import os
import subprocess
import sys
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad')


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def ordmod(r, m):
    x, t = r % m, 1
    while x != 1:
        x = x * r % m
        t += 1
    return t


def actions(p, k):
    """one r per subgroup <r> of Z_p^* of order dividing k (r = generator), order > 1; isomorphism classes of
    Z_p x|_r Z_k for fixed (p,k) correspond to the order k0 = ord(r) | gcd(k, p-1) (all r of the same order give
    isomorphic groups: Z_p x|_r Z_k = Z_p x|_{r^u} Z_k via j -> j/u when gcd(u,k)=1 ... only if such u exists; to be
    safe we list every r of order k0 up to the relabelling j -> u j with u in Z_k^*)."""
    g = None
    for c in range(2, p):
        if ordmod(c, p) == p - 1:
            g = c
            break
    out = []
    from math import gcd
    for k0 in range(2, p):
        if (p - 1) % k0 or k % k0:
            continue
        h = pow(g, (p - 1) // k0, p)          # an element of order k0
        rs = sorted({pow(h, e, p) for e in range(1, k0) if gcd(e, k0) == 1})
        # relabelling j -> u j (u in Z_k^*) maps r to r^u; keep one r per orbit
        seen = set()
        for r in rs:
            if r in seen:
                continue
            orb = {pow(r, u, p) for u in range(1, k) if gcd(u, k) == 1}
            seen |= orb
            out.append((r, k0))
    return out


def run(p, k, r, k0, Delta, D, threads, maxprint=5):
    plan = os.path.join(SP, f'plan_{p}_{k}_{r}.txt')
    lines = []
    for j1 in range(1, k):
        if pow(r, j1, p) == 1:
            continue
        for j2 in range(k):
            lines.append(f'{0 * k + j1} {1 * k + j2}\n')
    with open(plan, 'w') as f:
        f.writelines(lines)
    env = dict(os.environ, THREADS=str(threads), QFILTER="1")
    out = subprocess.run([os.path.join(HERE, 'hx'), 'meta', str(p), str(k), str(r), str(Delta), str(D), plan,
                          str(maxprint)], capture_output=True, text=True, env=env).stdout
    sols = [l for l in out.splitlines() if l.startswith('SOL')]
    done = [l for l in out.splitlines() if l.startswith('DONE')][0].split()
    tested, nsol, best = int(done[2]), int(done[4]), int(done[6])
    os.remove(plan)
    return tested, nsol, best, sols


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--faithful', action='store_true')
    ap.add_argument('--kmin', type=int, default=2)
    ap.add_argument('--maxsets', type=float, default=5e7)
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--maxprint', type=int, default=5)
    a = ap.parse_args()
    outdir = os.path.join(HERE, 'runs', f'frob_d{a.Delta}D{a.D}')
    os.makedirs(outdir, exist_ok=True)
    rows = []
    for p in primes_upto(a.nmax):
        for k in range(a.kmin, min(a.nmax // p, p) + 1):
            N = p * k
            if N < a.nmin or N > a.nmax:
                continue
            for r, k0 in actions(p, k):
                if a.faithful and k0 != k:
                    continue
                sets = (k - 1) * k * (comb(N - 3, a.Delta - 3) if a.Delta > 3 else 1)
                if sets > a.maxsets:
                    print(f'{p} {k} {r} {k0} {N} {2*N} skip sets={sets:.3g}', flush=True)
                    continue
                tested, nsol, best, sols = run(p, k, r, k0, a.Delta, a.D, a.threads, a.maxprint)
                print(f'{p} {k} {r} {k0} {N} {2*N} tested={tested} solutions={nsol} best={best}', flush=True)
                if nsol:
                    with open(os.path.join(outdir, f'meta_{p}_{k}_{r}.txt'), 'w') as f:
                        f.write(f'# Haar graph Delta={a.Delta} D={a.D} G=Z_{p} x|_{r} Z_{k} (ord r={k0}) N={N} n={2*N}; '
                                f'elements a*k+j; {nsol} normal-form solutions\n')
                        f.write('\n'.join(sols) + '\n')
