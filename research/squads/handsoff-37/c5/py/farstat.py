import sys
from collections import deque, Counter
toks = open(sys.argv[1]).read().split(); n = int(toks[0])
N = [[] for _ in range(n)]
for i in range(1, len(toks), 2):
    a, b = int(toks[i]), int(toks[i+1]); N[a].append(b); N[b].append(a)
m = n // 2
far_cnt = [0]*n; pairs = set()
for s in range(n):
    d = [-1]*n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in N[x]:
            if d[y] < 0: d[y] = d[x]+1; q.append(y)
    for t in range(n):
        if d[t] > 7 or d[t] < 0:
            far_cnt[s] += 1
            if s < t: pairs.add((s, t))
print("unordered far", len(pairs))
print("far pairs by side (AA, BB, AB):", Counter(('A' if s < m else 'B') + ('A' if t < m else 'B') for s, t in pairs))
fixed = [v for v in range(n) if (v < m and v >= 3*((m-int(sys.argv[2]))//3)) or (v >= m and v - m >= 3*((m-int(sys.argv[3]))//3))]
print("fixed vertices:", fixed, "far counts:", [far_cnt[v] for v in fixed])
print("far count distribution over vertices:", Counter(far_cnt).most_common(8))
