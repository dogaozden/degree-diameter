"""Climb N for one degree: try metacyclic groups Z_m x|_lam Z_k of order N with haar_search.

Usage: python3 drive.py d N_start N_stop secs_per_group [max_groups_per_N] [kmax]
For each N (ascending, step 1) list groups (m, k, lam) with m*k = N, 2 <= k <= kmax,
lam a generator of a cyclic subgroup of Z_m^* of order k' | k, k' > 1 (one lam per subgroup),
non-abelian only. Try up to max_groups_per_N of them (Frobenius-like first: k' = k, m prime).
On success writes sols/d{d}_N{N}.txt, builds graphs/haar_d{d}_n{2N}.json and moves to N+1.
Stops after N_stop or after 'fails' consecutive N values with no success.
"""
import math
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def is_prime(n):
    return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))


def mult_order(a, m):
    if math.gcd(a, m) != 1:
        return None
    o, x = 1, a % m
    while x != 1 % m:
        x = x * a % m
        o += 1
    return o


def groups(N, kmax):
    out = []
    for k in range(2, kmax + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        seen = set()
        for lam in range(2, m):
            o = mult_order(lam, m)
            if o is None or o == 1 or k % o:
                continue
            sub = frozenset(pow(lam, e, m) for e in range(o))
            if sub in seen:
                continue
            seen.add(sub)
            # score: prefer faithful action (o == k), prime m, larger o
            score = (o == k) * 4 + is_prime(m) * 2 + o / k - (k == 2) * 5 - abs(k - 5) * 0.2
            out.append((-score, m, k, lam))
    out.sort()
    return [(m, k, lam) for _, m, k, lam in out]


def main():
    d, N0, N1, secs = map(int, sys.argv[1:5])
    maxg = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    kmax = int(sys.argv[6]) if len(sys.argv) > 6 else 16
    fails = 0
    N = N0
    while N <= N1 and fails < 12:
        gs = groups(N, kmax)[:maxg]
        won = False
        for (m, k, lam) in gs:
            sol = os.path.join(HERE, "sols", f"d{d}_N{N}.txt")
            r = subprocess.run([os.path.join(HERE, "haar_search"), str(d), str(m), str(k), str(lam),
                                str(N), str(secs), sol], capture_output=True, text=True)
            print(r.stdout.strip(), flush=True)
            if " best=0 " in r.stdout:
                out = os.path.join(HERE, "graphs", f"haar_d{d}_n{2 * N}.json")
                subprocess.run([sys.executable, os.path.join(HERE, "build_haar.py"), sol, out])
                won = True
                break
        if gs:
            fails = 0 if won else fails + 1
        N += 1


if __name__ == "__main__":
    main()
