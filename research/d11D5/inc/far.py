"""Far point-line pairs (pure distance >= 5) and short cycles of a base (plusopt format).  usage: python3 far.py in.txt"""
import sys, numpy as np
f = open(sys.argv[1]).read().split(); n, dg = int(f[0]), int(f[1])
ln = np.array(f[2:2 + n * dg], dtype=int).reshape(n, dg)
I = np.zeros((n, n), dtype=np.int64)
for l in range(n): I[ln[l], l] = 1
PP = I @ I.T; d3 = I + PP @ I          # walks of length 1 and 3 point->line
far = (d3 == 0)
print("far point-line pairs", far.sum(), "(girth-8 minimum would be", n, ")  per line max", far.sum(0).max(), " per point max", far.sum(1).max())
c4 = ((PP - np.diag(np.diag(PP))) > 1).sum() // 2
print("point pairs on >= 2 common lines (4-cycles):", c4)
