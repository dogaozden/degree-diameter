# For each K, find a multiset of cores (orders 2,3,4,5 => sizes 7,13,21,31) with sum K, using conservative caps.
N = {2:7, 3:13, 4:21, 5:31}
def feasible(ms):
    m = len(ms)
    if m == 1: return True
    if 5 in ms and m > 7: return False
    if 4 in ms and m > 10: return False
    if m > 11: return False
    return True
best = {}
import itertools
def rec(sofar, minidx, cnt, K):
    pass
# enumerate multisets with sum <= 260
opts = [5,4,3,2]
res = {}
def gen(idx, ms, tot):
    if idx == len(opts):
        if ms and tot <= 260 and feasible(ms):
            res.setdefault(tot, sorted(ms, reverse=True))
        return
    s = opts[idx]
    k = 0
    while True:
        m2 = ms + [s]*k
        t2 = tot + N[s]*k
        if t2 > 260 or len(m2) > 11: break
        gen(idx+1, m2, t2)
        k += 1
gen(0, [], 0)
M = 0
for K in range(7, 260):
    if K <= 100 or K in res: M = K
    else: break
print("coverage by cliques+windows, first gap:", M+1)
gaps = [K for K in range(94, 260) if K not in res]
print("gaps (no clique multiset) above 93:", gaps[:20])
for K in range(94, 175):
    if K in res: print(K, res[K], end=" | ")
