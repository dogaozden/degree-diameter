import sys
sys.path.insert(0, '.')
from uncrowd import P, Lp, lines, lof
fl = [tuple(map(int, t.split(':'))) for t in sys.argv[1].split()]
pc = sum(1 for i in range(len(fl)) for j in range(i+1, len(fl)) if fl[j][0] in P[fl[i][0]])
lc = sum(1 for i in range(len(fl)) for j in range(i+1, len(fl)) if fl[j][1] in Lp[fl[i][1]])
inc = all(p in lines[l] for p, l in fl)
print('k', len(fl), 'collinear point pairs', pc, 'concurrent line pairs', lc, 'all flags incident', inc)
