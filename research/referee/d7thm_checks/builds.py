#!/usr/bin/env python3
"""Referee check: the slot vectors and orders printed in the make logs of job conics-2 (branch
claude/conics-2-diameter-7-ic0oat, research/synthetic/conics2/d*D7/make*.log) against the formulas of Section 2 of
D7_THEOREMS.md, computed here from q, the type string, |R_H| = (q+1)(q^3+1), |R_L| and m read from the log's own
description of the sets.  Usage: builds.py <conics2 dir>"""
import re, sys, glob, os
d = sys.argv[1]
def N(q): return (q + 1)*(q**4 + q**2 + 1)
def rot(L):
    k = (L - 1)//2
    return [(j, (j + i) % L) for j in range(L) for i in range(1, k + 1)]
allok = True
for f in sorted(glob.glob(os.path.join(d, 'd*D7', 'make*.log'))):
    s = open(f).read()
    q = int(re.search(r'^q = (\d+)', s, re.M).group(1))
    RH = int(re.search(r'R_H = spread points \((\d+)', s).group(1))
    RL = int(re.search(r'R_L = [^(]*\((\d+)', s).group(1))
    nu0 = 'nu = 0' in s.split('R_L =')[1].split('\n')[0]
    m = int(re.search(r"\|R'\| = (\d+)", s).group(1))
    T = re.search(r'types (\w+):', s).group(1)
    al_log = eval(re.search(r'free A-slots per level (\[[^\]]*\])', s).group(1))
    be_log = eval(re.search(r'B-slots (\[[^\]]*\])', s).group(1))
    KB, KA = map(int, re.search(r'hubs per side (\d+) (\d+)', s).group(1, 2))
    n = int(re.search(r'^n = (\d+)', s, re.M).group(1))
    P = (q + 1)*(q**3 + 1); Lam = q**4 + q**2 + q if nu0 else q**4 + q
    L = len(T); al = [0]*L; be = [0]*L
    for (i, j) in rot(L):
        x = (P if T[i] == 'H' else Lam) if T[i] != T[j] else m
        al[i] += x; be[j] += x
    n_f = 2*L*N(q) + KA + KB
    ok = (RH == P and RL == Lam and al == al_log and be == be_log and KB <= min(al) and KA <= min(be) and n == n_f)
    allok &= ok
    print('%-24s q=%2d %-9s |R_H|=%d |R_L|=%d%s m=%d  slots min (%d,%d)  hubs (%d,%d)  n=%d formula %d  %s' % (
        os.path.relpath(f, d), q, T, RH, RL, ' (with S_0)' if nu0 else '', m, min(al), min(be), KB, KA, n, n_f,
        'OK' if ok else 'MISMATCH'))
print('all make logs consistent with the formulas:', allok)
