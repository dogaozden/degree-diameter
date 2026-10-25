"""Write the Z_5 polygon-cover bases X of H(q) + 2 random matchings (models5k f5k, k = 1) used by
geodcount.c and nbwalk.c.  usage: python3 polycover_counts.py q seed out.txt"""
import sys

import gh
import models5k

q, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
NB, edges = models5k.build(q, 1, 'f5k', seed, gh.load(q))
gh.write_base(out, NB, 5, 1, edges)
