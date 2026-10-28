#!/usr/bin/env python3
"""Aggregate far.c outputs: table of (least norm, pure at least norm) and the pure-norm<=50 explanation score."""
import glob, re, collections
rows = []
per = []
for f in sorted(glob.glob('/home/user/degree-diameter/research/squads/thmfam-r1/c9/out_p*_q*.txt')):
    lines = open(f).read().splitlines()
    m = re.match(r'SUMMARY p=(\d+) q=(\d+) .*ecc\(e,A\)=(\d+) A_vertices_in_component=(\d+) far_A=(\d+) listed=(\d+)', lines[0])
    p, q, ecc, comp, far, listed = map(int, m.groups())
    leg = 1 if pow(p, (q - 1) // 2, q) == 1 else -1
    nl = 0; expl = 0; cnt = collections.Counter(); ok_any = 0
    for ln in lines[1:]:
        a0, a1, a2, a3, g, N, pureN, p50, _ = ln.split()
        N = int(N); pureN = int(pureN); p50 = int(p50)
        nl += 1
        expl += p50
        ok_any += (N >= 0)
        cnt[(N if N >= 0 else 'none', 'pure' if pureN else ('nonpure' if N >= 0 else '-'))] += 1
    per.append((p, q, leg, ecc, comp, far, nl, expl, ok_any))
    for k, v in cnt.items(): rows.append((p, q, k, v))
print('p q (p/q) ecc |A-comp| far_A listed | pure<=50 frac | any gamma<=200 frac')
for r in per:
    p, q, leg, ecc, comp, far, nl, expl, ok_any = r
    print(f'{p} {q} {leg:+d} {ecc} {comp} {far} {nl} | {expl}/{nl}={expl/nl:.3f} | {ok_any}/{nl}={ok_any/nl:.3f}')
tot = sum(r[6] for r in per); totexpl = sum(r[7] for r in per); totany = sum(r[8] for r in per)
print(f'TOTAL listed={tot} pure_le50={totexpl} frac={totexpl/tot:.4f} any_le200={totany/tot:.4f}')
agg = collections.Counter()
for p, q, k, v in rows: agg[k] += v
print('\nTable (least norm of gamma, pure at that norm?, count) pooled over all runs:')
print('norm  pure?     count')
def key(k):
    n = k[0]; return (10**9 if n == 'none' else n, k[1])
for k in sorted(agg, key=key):
    print(f'{str(k[0]):>5} {k[1]:>8} {agg[k]:>8}')
