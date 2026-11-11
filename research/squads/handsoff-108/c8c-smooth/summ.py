#!/usr/bin/env python3
# summ.py LOG [LOG...]: chain minima (ORBW=3 energy) and evals per chain from CHAIN lines of haar_sym2-style logs
import sys, re, math, statistics as st
def chains(path):
    out = []
    for line in open(path, errors='replace'):
        if line.startswith('CHAIN '):
            m = re.match(r'CHAIN \d+ min (\d+) secs \d+ evals (\d+)', line)
            if m: out.append((int(m.group(1)), int(m.group(2))))
    return out
def mwu(a, b):   # two-sided Mann-Whitney U, normal approximation with ties
    n1, n2 = len(a), len(b)
    allv = sorted([(x, 0) for x in a] + [(x, 1) for x in b])
    ranks = [0.0] * len(allv); i = 0
    while i < len(allv):
        j = i
        while j + 1 < len(allv) and allv[j + 1][0] == allv[i][0]: j += 1
        for k in range(i, j + 1): ranks[k] = (i + j) / 2 + 1
        i = j + 1
    r1 = sum(r for r, (v, g) in zip(ranks, allv) if g == 0)
    u1 = r1 - n1 * (n1 + 1) / 2
    mu = n1 * n2 / 2; sd = math.sqrt(n1 * n2 * (n1 + n2 + 1) / 12)
    z = (u1 - mu) / sd if sd > 0 else 0
    return u1 / (n1 * n2), 2 * (1 - 0.5 * (1 + math.erf(abs(z) / math.sqrt(2))))
for p in sys.argv[1:]:
    c = chains(p); mins = [m for m, e in c]
    if not mins: print(p, 'no chains'); continue
    ev = [e for m, e in c]
    s = sorted(mins)
    print(f"{p}: chains={len(mins)} min={s[0]} p10={s[len(s)//10]} median={st.median(mins)} mean={st.mean(mins):.1f} "
          f"<=12: {sum(m<=12 for m in mins)} <=9: {sum(m<=9 for m in mins)} <=6: {sum(m<=6 for m in mins)} "
          f"mean evals/chain={st.mean(ev):.0f} total evals={sum(ev)}")
if len(sys.argv) == 3:
    a = chains(sys.argv[1]); b = chains(sys.argv[2])
    if a and b:
        auc, pv = mwu([m for m, e in a], [m for m, e in b])
        print(f"Mann-Whitney P(first chain min > second) = {auc:.3f}  two-sided p = {pv:.3f}  (first = {sys.argv[1]})")
