"""Expand a quotient independent set (quotient indices, one per line) to the point set of the orbits.
usage: expand.py PREFIX SOLFILE OUT   (PREFIX_orb.bin: quotient index -> orbit id; PREFIX_porb.bin: point -> orbit id)"""
import sys, numpy as np
prefix, solf, outf = sys.argv[1:4]
qorb = np.fromfile(prefix + '_orb.bin', dtype=np.int32)
porb = np.fromfile(prefix + '_porb.bin', dtype=np.int32)
chosen = [int(x) for x in open(solf).read().split()]
orbs = set(int(qorb[i]) for i in chosen)
pts = np.nonzero(np.isin(porb, list(orbs)))[0]
open(outf, 'w').write('\n'.join(map(str, pts.tolist())) + '\n')
print('orbits', len(orbs), 'points', len(pts))
