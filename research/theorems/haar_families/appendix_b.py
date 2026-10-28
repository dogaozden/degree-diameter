"""Appendix B of HAAR_FAMILIES.md: for Delta = p+1 and D = 7..12, the largest LPS graph Gamma_{p,q} (q prime, p < q <=
scan limit) with diameter <= D, from scan/lps_p*.txt; the largest q allowed by Theorem 3.2 (q^2 < 2 p^floor(D/2));
the 2013 table and the lab's records.  Prints a Markdown table."""
import re, glob, math, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
from family_score import TABLE, OURS
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5) + 1))
data = {}
for f in glob.glob('scan/lps_p*.txt'):
    for L in open(f):
        m = re.search(r'p=(\d+) q=(\d+) .*vertices=(\d+).*diameter=(\d+)', L)
        if m:
            p, q, n, d = map(int, m.groups()); data[(p, q)] = (n, d)
limit = {}
for (p, q) in data: limit[p] = max(limit.get(p, 0), q)
print('| Δ (p) | D | q | vertices | % Moore | Thm 3.2: q ≤ | table | table / LPS | lab record |')
print('|---|---|---:|---:|---:|---:|---:|---:|---:|')
for p in sorted(limit):
    for D in range(7, 13):
        best = max(((n, q) for (pp, q), (n, d) in data.items() if pp == p and d <= D), default=None)
        if not best: continue
        n, q = best
        W = 2 * sum(p**j for j in range(D))
        qmax = max(x for x in range(3, 10**5) if isprime(x) and x * x < 2 * p**(D // 2)) if 2 * p**(D//2) > 9 else 0
        lim = '*' if q == limit[p] or qmax > limit[p] and not any(d > D for (pp, qq), (nn, d) in data.items() if pp == p and qq > q) else ''
        t = TABLE.get((p + 1, D)); o = OURS.get((p + 1, D))
        ratio = f'{t / n:.1f}' if t else '–'
        print(f'| {p+1} ({p}) | {D} | {q}{lim} | {n:,} | {100*n/W:.2f} | {qmax} | {t:,} | {ratio} | {o:,} |' if t and o else
              f'| {p+1} ({p}) | {D} | {q}{lim} | {n:,} | {100*n/W:.2f} | {qmax} | {f"{t:,}" if t else "–"} | {ratio} | {f"{o:,}" if o else "–"} |')
print(f'\nScan limits: ' + ', '.join(f'p = {p}: q ≤ {limit[p]}' for p in sorted(limit)) + '.')
