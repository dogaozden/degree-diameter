"""Which cells (Delta, D), Delta <= 16, 3 <= D <= 10, can a route-chart lift reach at all?
A chart lift with k letters over F_q has a k-regular bipartite controller of diameter <= D (lifted walks project to
controller walks), fibre F_q^(D-1) (D-1 = the binding walk length), so its order is at most q^(D-1) * Moore_b(k, D),
where Moore_b(k, D) = 2(1 + (k-1) + ... + (k-1)^(D-1)).  A cell is reachable only if this ceiling exceeds the best
known value.  'realistic' uses the best known n_b(k, D) (table / lab) instead of the Moore bound.
Table values: research/frontier/heuristic.py TABLE (DS14v2 2013) with the lab's raised cells from research/RESULTS.md."""
import sys
sys.path.insert(0, '../../frontier')
from heuristic import TABLE
LAB = {(4, 5): 162, (5, 5): 354, (7, 5): 1152, (8, 5): 1764, (9, 5): 2662, (11, 3): 192, (13, 3): 276, (15, 3): 376,
       (16, 3): 396, (7, 4): 359, (11, 4): 1782, (13, 4): 3146, (15, 4): 5070, (16, 4): 5440, (16, 5): 33792,
       (12, 5): 8748, (7, 6): 9592, (11, 6): 148944, (13, 6): 388972, (15, 6): 870440, (16, 6): 940846,
       (3, 8): 288, (5, 7): 3120, (5, 8): 9576, (5, 9): 28560, (5, 10): 95472, (4, 10): 12416, (6, 7): 8880,
       (6, 8): 31680, (6, 9): 127296, (6, 10): 524160, (7, 8): 95760, (7, 9): 462840, (7, 10): 2237760,
       (8, 7): 43344, (8, 8): 239904, (8, 9): 1326960, (8, 10): 7818096, (9, 8): 540360, (9, 9): 3499776,
       (9, 10): 23975280, (10, 9): 8003856, (10, 10): 60141120, (11, 8): 2258520, (11, 9): 16792080,
       (12, 9): 34026720, (12, 10): 325832976, (13, 8): 6814080, (13, 9): 67742688, (13, 10): 677714400,
       (14, 9): 116068656, (14, 10): 1326627120, (15, 8): 18128880, (15, 9): 208029120, (16, 9): 337394400}
def best(d, D):
    t = TABLE[d][D - 3]
    v = [x for x in (t, LAB.get((d, D))) if x is not None]
    return max(v) if v else None
def moore(k, D): return 2 * sum((k - 1) ** i for i in range(D))
def pp(q):
    for p in range(2, q + 1):
        if q % p == 0:
            while q % p == 0: q //= p
            return q == 1
    return False
rows = []
for d in range(3, 17):
    for D in range(3, 11):
        b = best(d, D)
        if b is None: continue
        for k in range(3, d + 1):
            if d % k: continue
            q = d // k
            if q < 2 or not pp(q): continue
            ceil = q ** (D - 1) * moore(k, D)
            nbk = best(k, D)
            real = q ** (D - 1) * nbk if nbk else None
            rows.append((d, D, k, q, b, ceil, real))
print('cells where the Moore ceiling q^(D-1)*Moore_b(k,D) exceeds the best known value (k >= 3):')
print('(Delta,D)  k  q   best known    ceiling     q^(D-1)*n_b(k,D) [best known controller order]')
for d, D, k, q, b, ceil, real in rows:
    if ceil > b:
        print('(%2d,%2d)   %d  %d  %12d %12d %14s %s' % (d, D, k, q, b, ceil, real, '<-- even a record controller is too small' if real and real <= b else ''))
print()
print('cells with no chance (ceiling <= best known):', sum(1 for r in rows if r[5] <= r[4]), 'of', len(rows), '(cell, k, q) combinations')
