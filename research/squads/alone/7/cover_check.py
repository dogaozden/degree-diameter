"""Independent check of the cover obstruction. A connected covering H -> X of the flag graph with fibre size k >= 2
has diameter > 5 whenever some same-side target v has fewer than k non-backtracking walks of length <= 4 from a source u.
Here: enumerate every non-backtracking path of length 2 and 4 from one source per side by explicit DFS (no DP),
count per same-side endpoint, and list the targets with exactly one walk.  usage: python3 cover_check.py EDGES"""
import sys
from collections import Counter

with open(sys.argv[1]) as f:
    n = int(f.readline())
    adj = [[] for _ in range(n)]
    for line in f:
        a, b = map(int, line.split())
        adj[a].append(b)
        adj[b].append(a)
nA = n // 2

def paths(src, maxlen):
    ends = Counter()
    stack = [(src, -1, 0)]
    while stack:
        x, prev, L = stack.pop()
        if L in (2, 4):
            ends[x] += 1
        if L == maxlen:
            continue
        for y in adj[x]:
            if y != prev:
                stack.append((y, x, L + 1))
    return ends

for src in (0, nA):
    ends = paths(src, 4)
    side = range(0, nA) if src < nA else range(nA, n)
    targets = [v for v in side if v != src]
    one = [v for v in targets if ends.get(v, 0) == 1]
    zero = [v for v in targets if ends.get(v, 0) == 0]
    print(f"source {src}: same-side targets {len(targets)}, walks ending at target: total {sum(ends[v] for v in targets)}, "
          f"targets with exactly 1 walk: {len(one)}, with 0 walks: {len(zero)}, "
          f"walks ending at source (closed, len 4): {ends.get(src, 0)}")
