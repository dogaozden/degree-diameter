#!/usr/bin/env python3
"""Dual segment set checker (D7_HEXAGON.md Definition 1.3): a set G of lines of H(q) such that for every line of G the
other lines of G meeting it all pass through one point of it. Prints |G| and whether G is a dual segment set; with
--points, checks a segment set of points instead.  usage: dualseg_check.py HEXBIN FILE [--points]"""
import sys
import numpy as np
from hexload import load

q, N, LP, PL, X = load(sys.argv[1])
G = np.unique(np.array([int(t) for t in open(sys.argv[2]).read().split()], dtype=np.int64))
if '--points' in sys.argv:
    LP, PL = PL, LP
inG = np.zeros(N, bool); inG[G] = True
cnt = inG[PL].sum(1)                                    # G-lines through each point
bad = int(((cnt[LP[G]] >= 2).sum(1) > 1).sum())          # lines of G with two or more points shared with G
print(f'q={q} size={len(G)} valid={bad == 0} bad_lines={bad}')
