"""Fiber balance of the metacyclic records over their quotients.

For G = Z_m x|_r Z_k and a prime d | m (or d = 1), Q_d = Z_d x|_r Z_k is a quotient of G with fibers of size m/d.
Non-backtracking walks of H(G,S) project to H(Q_d, S mod d).  W_q = number of NB walks of the right parity and length
<= D-1 from the source that land on q (D even: source (e,A), targets B; D odd: both sources, targets on the same side).
  slack_d = min_q W_q / (m/d)       (rigorous: must be >= 1)
  mu_d    = sum_q (m/d) exp(-W_q/(m/d))   (Poisson estimate of uncovered vertices if each fiber were filled at random)
  mu_unif = N exp(-W/N) per condition     (the same total spread evenly)
For each record we compare with random S in the same group (a-parts and j-parts uniform, e kept): percentile of the
record's mu_d among random S.  Output: runs/fibers_out.txt.
"""
import os
import random
import sys
from math import exp, log

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from meta import all_solutions  # noqa: E402


def prime_factors(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def walk_counts(d, k, r, S, D, startB):
    """NB walk counts on H(Q_d, S) with Q_d = Z_d x|_r Z_k, element index a*k + j; returns counts on the target side."""
    n = d * k
    Delta = len(S)
    rp = [pow(r, j, d) if d > 1 else 0 for j in range(k)]
    # left multiplication by s and by s^-1 as index arrays
    A = np.arange(d)[:, None]
    J = np.arange(k)[None, :]

    def lmul(s):
        a, j = s
        return (((a + (rp[j % k] if d > 1 else 0) * A) % d) * k + (j + J) % k).reshape(-1)

    def inv(s):
        a, j = s
        jj = (-j) % k
        return ((-(rp[jj] if d > 1 else 0) * a) % d if d > 1 else 0, jj)

    Sd = [(a % d if d > 1 else 0, j % k) for (a, j) in S]
    Lm = [lmul(s) for s in Sd]
    Li = [lmul(inv(s)) for s in Sd]
    # state arrays cur[side][last][v]
    L = Delta + 1
    cur = np.zeros((2, L, n), dtype=np.float64)
    side0 = 1 if startB else 0
    cur[side0, Delta, 0] = 1.0
    tside = (1 - side0) if D % 2 == 0 else side0
    tot = np.zeros(n)
    if tside == side0:
        tot[0] += 1
    for length in range(1, D):
        nxt = np.zeros_like(cur)
        for s in range(2):
            for l in range(L):
                c = cur[s, l]
                if not c.any():
                    continue
                for t in range(Delta):
                    if t == l:
                        continue
                    perm = Lm[t] if s == 0 else Li[t]
                    np.add.at(nxt[1 - s, t], perm, c)
        cur = nxt
        sn = (side0 + length) % 2
        if sn == tside:
            tot += cur[sn].sum(axis=0)
    return tot


def stats(m, k, r, S, D, d):
    K = m // d
    res = []
    for startB in ([False] if D % 2 == 0 else [False, True]):
        W = walk_counts(d, k, r, S, D, startB)
        res.append(W)
    slack = min(W.min() for W in res) / K
    mu = sum(float((K * np.exp(-W / K)).sum()) for W in res)
    Wtot = sum(float(W.sum()) for W in res) / len(res)
    N = m * k
    mu_unif = len(res) * N * exp(-Wtot / N)
    return slack, mu, mu_unif


def main():
    random.seed(1)
    sols = [s for s in all_solutions() if s['D'] >= 7]
    out = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'fibers_out.txt'), 'w')

    def say(*a):
        print(*a)
        print(*a, file=out)
        out.flush()

    say('cell | m k r | quotient Q_d (d) | record: slack mu_d/mu_unif | random S (200): median slack, median '
        'mu_d/mu_unif, P(slack<1) | record percentile of mu_d (lower = better balanced)')
    for s in sols:
        m, k, r, S, D = s['m'], s['k'], s['r'], s['S'], s['D']
        for d in [1] + prime_factors(m):
            if d * k > 20000:
                continue
            sl, mu, mu_u = stats(m, k, r, S, D, d)
            rs, rmu, bad = [], [], 0
            for _ in range(200):
                T = [S[0]] + [(random.randrange(m), random.randrange(k)) for _ in range(len(S) - 1)]
                a, b, c = stats(m, k, r, T, D, d)
                rs.append(a)
                rmu.append(b / c)
                bad += a < 1
            pct = sum(x <= mu / mu_u for x in rmu) / len(rmu)
            say(f"({s['Delta']},{D}) | {m} {k} {r} | d={d} |K|={m//d} | {sl:.2f} {mu/mu_u:.3f} | "
                f"{np.median(rs):.2f} {np.median(rmu):.3f} {bad/200:.2f} | {pct:.2f}")


if __name__ == '__main__':
    main()
