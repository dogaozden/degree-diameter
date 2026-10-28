"""Expand a quotient solution (quotient vertex ids, one per line) to the point set.
usage: expand.py TAG SOLFILE OUTFILE   (TAG = S19 or S7; TAG_orb.bin maps quotient ids to orbit ids, TAG_porb.bin points to orbits)"""
import sys, numpy as np
tag, solf, outf = sys.argv[1:4]
out = '/home/user/degree-diameter/research/squads/polylev/r2/e02/'
qorb = np.fromfile(out + tag + '_orb.bin', dtype=np.int32)
porb = np.fromfile(out + tag + '_porb.bin', dtype=np.int32)
qv = [int(x) for x in open(solf).read().split()]
chosen_orbs = np.zeros(porb.max() + 1, dtype=bool)
chosen_orbs[qorb[qv]] = True
pts = np.nonzero(chosen_orbs[porb])[0]
open(outf, 'w').write('\n'.join(map(str, pts.tolist())) + '\n')
print('quotient orbits', len(qv), 'points', len(pts))
