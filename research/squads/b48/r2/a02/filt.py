import sys
from math import lcm
from functools import reduce
sys.argv = ["x"]
exec(open("enumerate_groups.py").read().split("out.sort()")[0])
res = []
for order, k, spec in out:
    comps = [tuple(map(int, c.split(":"))) for c in spec.split(",")]
    L = reduce(lcm, [d for p, d in comps])
    if L != k:
        continue   # non-faithful (central cyclic part): skip
    res.append((order, k, spec))
res.sort()
for r in res:
    print(*r)
print(len(res), "faithful")
