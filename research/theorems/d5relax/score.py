"""Scorer for relaxed sets of W(q) (job d5-relax; squad scorer).  Recomputes collinearity from coordinates
(orbits.WSp: points of PG(3,q) with first non-zero coordinate 1 in itertools.product order, w = x0y2+x1y3-x2y0-x3y1).
A set is valid if every point of it is collinear with at most one other point of it.
usage: python3 score.py q FILE   (FILE: rtabu output "size\\n v\\n v ..." or a JSON list, or JSON {"T": [...]})"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orbits import WSp
q = int(sys.argv[1]); s = open(sys.argv[2]).read().strip()
if s.startswith('[') or s.startswith('{'):
    T = json.loads(s); T = T['T'] if isinstance(T, dict) else T
else:
    T = [int(x) for x in s.split()[1:]]
W = WSp(q); T = sorted(set(int(x) for x in T)); A = np.array(T)
ok = len(T) > 0 and A.min() >= 0 and A.max() < W.n
d = W.C[np.ix_(A, A)].sum(1) if ok else np.array([9])
valid = bool(ok and (d <= 1).all())
print(json.dumps(dict(q=q, size=len(T), pairs=int(d.sum()) // 2 if ok else 0, valid=valid)))
