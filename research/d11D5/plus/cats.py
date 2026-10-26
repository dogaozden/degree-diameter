import sys
from collections import Counter
n = int(sys.argv[2]); new = {n - 1: "x*", 2 * n - 1: "l*"}
rows = [tuple(map(int, l.split())) for l in open(sys.argv[1])]
def nm(v): return new.get(v, "P" if v < n else "L")
print(len(rows), Counter((nm(s), nm(t), c, d) for s, t, c, d in rows).most_common(12))
