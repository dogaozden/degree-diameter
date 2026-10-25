# Referee recomputation of A(Delta, D) (Theorem 4.3) and a finite-difference test of the parity-class polynomial remark.
from functools import lru_cache
import sys
sys.setrecursionlimit(10000)
# A(d,D) = #{c in Z^d : sum c = eps, sum|c| <= D-1}
def A(d,D):
    eps = 1 if D%2==0 else 0
    M = D-1
    # dp over coordinates: count[(sum, abs)]
    from collections import defaultdict
    cur = {(0,0):1}
    for _ in range(d):
        nxt = defaultdict(int)
        for (s,a),v in cur.items():
            for c in range(-(M-a), M-a+1):
                nxt[(s+c, a+abs(c))] += v
        cur = nxt
    return sum(v for (s,a),v in cur.items() if s==eps and a<=M)
claimed = {8:[48,216,780,2376,6328,15128,33111,67360,128876,234048,406458,679056,1096740,1719376],
9:[61,309,1251,4251,12559,33111,79459,176251,365751,716959,1337961,2392209,4119501,6862501],
10:[75,420,1875,7002,22645,65080,169515,406390,907753,1907940,3803865,7241430,13235895,23335504]}
for D in (8,9,10):
    mine=[A(d,D) for d in range(3,17)]
    print(D, mine==claimed[D], [ (d+3,m,c) for d,(m,c) in enumerate(zip(mine,claimed[D])) if m!=c])
# A(3,D) formula
print([ (D,A(3,D), 3*D*D/4 if D%2==0 else (3*D*D+1)/4) for D in range(2,14)])
# polynomial on parity classes? test degree-(d-1) fit by finite differences for d=4,5
import itertools
for d in (4,5,6):
    for par in (0,1):
        Ds=[D for D in range(2,40) if D%2==par][:d+3]
        vals=[A(d,D) for D in Ds]
        diffs=vals
        for _ in range(d): diffs=[b-a for a,b in zip(diffs,diffs[1:])]
        print('d',d,'parity',par,'d-th differences (should be 0 if poly deg d-1):',diffs)
