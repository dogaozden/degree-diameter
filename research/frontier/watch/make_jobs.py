"""Job lists for the frontier watcher sessions: groups M x Z_n (M = SL/PSL/PGL(2,p), p prime) with order in a range.

  python3 make_jobs.py d D lo hi seconds [seeds [nmax]] > jobs.txt
Each line is batch.sh format: d D seconds seed K group... n. Sorted by order, smallest first (smallest margin over
the target first, so a success comes early and later lines push the order up).
"""
import sys

def primes(n):
    s = [True] * (n + 1); s[0] = s[1] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = [False] * len(s[i * i::i])
    return [i for i, b in enumerate(s) if b]

d, D, lo, hi, secs = map(int, sys.argv[1:6])
seeds = int(sys.argv[6]) if len(sys.argv) > 6 else 2
nmax = int(sys.argv[7]) if len(sys.argv) > 7 else 50  # big cyclic factors make the group nearly abelian (weak)
cands = []
for p in primes(400):
    base = {'sl': p * (p * p - 1), 'pgl': p * (p * p - 1)}
    if p > 2: base['psl'] = p * (p * p - 1) // 2
    for g, o in base.items():
        if o > hi: continue
        for n in range(max(1, -(-lo // o)), hi // o + 1):
            if lo <= o * n <= hi and n <= nmax:
                cands.append((o * n, g, p, n))
seen = set()
for N, g, p, n in sorted(cands):
    if (N, g, p, n) in seen: continue
    seen.add((N, g, p, n))
    for s in range(1, seeds + 1):
        print(d, D, secs, s, 8, g, p, n)
