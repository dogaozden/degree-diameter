# check_gh8.py gh_8.txt: incidence graph of H(8): sizes, regularity, linearity, and BFS layers from a point and a line.
# Generalized hexagon of order (8,8): layers from a point are 1, 9, 72, 576, 4608, 36864, 32768 (distance 0..6).
import sys, collections
f = open(sys.argv[1]); P, q = map(int, f.readline().split())
lines = [list(map(int, f.readline().split())) for _ in range(P)]
assert all(len(set(l)) == q + 1 for l in lines), "line size"
pl = [[] for _ in range(P)]
for li, l in enumerate(lines):
    for p in l: pl[p].append(li)
assert all(len(x) == q + 1 for x in pl), "point degree"
# linear space: two lines share at most one point
pairs = set()
for l in lines:
    s = sorted(l)
    for i in range(len(s)):
        for j in range(i + 1, len(s)):
            assert (s[i], s[j]) not in pairs, "two points on two lines"
            pairs.add((s[i], s[j]))
print("P =", P, "L =", P, "q =", q, "points/line and lines/point = q+1: ok, linear space: ok")
# incidence graph: vertices 0..P-1 points, P..2P-1 lines
adj = [[] for _ in range(2 * P)]
for li, l in enumerate(lines):
    for p in l:
        adj[p].append(P + li); adj[P + li].append(p)
def bfs(s):
    d = [-1] * (2 * P); d[s] = 0; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    cnt = collections.Counter(d)
    return max(d), [cnt[k] for k in range(max(d) + 1)], min(d)
for name, s in (("point 0", 0), ("line 0", P)):
    ecc, layers, mn = bfs(s)
    print(name, "eccentricity", ecc, "layer sizes", layers, "connected" if mn == 0 else "NOT CONNECTED")
