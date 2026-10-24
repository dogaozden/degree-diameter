"""write GF(q) add/mul tables for the C programs: q, then q*q add, then q*q mul"""
import sys
from gf import GF
q = int(sys.argv[1]); F = GF(q)
with open(sys.argv[2], 'w') as f:
    f.write('%d\n' % q)
    f.write(' '.join(str(F.add[a][b]) for a in range(q) for b in range(q)) + '\n')
    f.write(' '.join(str(F.mul[a][b]) for a in range(q) for b in range(q)) + '\n')
