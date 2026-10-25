#!/usr/bin/env python3
"""star.py IN.sol OUT.sol: impose the "star" condition for the FLAGDEL variant: for each freed flag (p, l), sigma maps
the non-freed points of l other than p onto non-freed lines through p (other than l), by swaps (max matching).
Prints the number of star conditions met / possible and the coverage before and after."""
import sys
import numpy as np
import lns
S = lns.read_sol(sys.argv[1]); F = S['F']; sig = S['sig'].copy(); N = len(sig)
isfree = np.zeros(N, bool); isfree[F] = True
fl = set(int(sig[p]) for p in F)
print('cover before', lns.cover(F, sig, S['hubadj']))
fixed = set(); met = 0; poss = 0
for p in F:
    l = int(sig[p])
    ys = [int(y) for y in lns.PTS[l] if y != p and not isfree[y]]
    Ls = [int(L) for L in lns.LOF[p] if L != l and int(L) not in fl]
    poss += min(len(ys), len(Ls))
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    # keep the ys that already map to a line in Ls; assign the rest
    have = [y for y in ys if int(sig[y]) in Ls]
    freeL = [L for L in Ls if int(sinv[L]) not in have]
    for y in ys:
        if y in have or not freeL: continue
        L = freeL.pop(0); o = int(sinv[L])
        if o in fixed or isfree[o]: continue
        sig[o], sig[y] = sig[y], L
        sinv[sig[o]] = o; sinv[L] = y
    for y in ys:
        if int(sig[y]) in Ls: fixed.add(y); met += 1
print('star conditions met', met, 'of', poss, '(points on freed lines: %d)' % sum(1 for p in F for y in lns.PTS[sig[p]] if y != p))
print('cover after', lns.cover(F, sig, S['hubadj']))
lns.write_sol(sys.argv[2], S, sig, -1)
open(sys.argv[2] + '.fixed', 'w').write(' '.join(map(str, sorted(fixed))) + '\n')
