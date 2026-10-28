"""Expand orbit solutions to element sets and verify both sides.
usage: expand_verify.py SIDE QUOTIENT_TAG SOLFILE OUTFILE  (SIDE = points|lines; orbits from S73.porb / S73.lorb)"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
side, tag, solf, outf = sys.argv[1:5]
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q8.bin')
orb = np.fromfile('S73.porb' if side == 'points' else 'S73.lorb', dtype=np.int32)
qids = np.fromfile(f'{tag}_orb.bin', dtype=np.int32)
chosen_q = [int(x) for x in open(solf).read().split()]
orbs = set(int(qids[i]) for i in chosen_q)
elems = sorted(int(v) for v in np.nonzero(np.isin(orb, list(orbs)))[0])
if side == 'lines':
    S = set(elems)
    cover = np.zeros(H.N, dtype=np.int64)
    for l in elems:
        cover[H.lines[l]] += 1
    ok = bool((cover <= 1).all())
    print('lines:', len(elems), 'pairwise disjoint:', ok)
else:
    S = set(elems)
    cnt = np.zeros(H.L, dtype=np.int64)
    for p in elems:
        cnt[H.PL[p]] += 1
    ok = bool((cnt <= 1).all())
    print('points:', len(elems), 'pairwise non-collinear:', ok)
open(outf, 'w').write('\n'.join(map(str, elems)) + '\n')
