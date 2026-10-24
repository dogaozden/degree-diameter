"""Non-backtracking walk multiplicities in the flag graph, from one source per side.
PGL(5,3) acts transitively on each side of the flag graph, so one source per side covers all same-side pairs.
For each same-side target v we count non-backtracking walks of length 2 and 4 from the source (the walks that can
realise a voltage in a regular lift). usage: python3 walks.py EDGES"""
import sys
from collections import Counter

with open(sys.argv[1]) as f:
    n = int(f.readline())
    adj = [[] for _ in range(n)]
    for line in f:
        a, b = map(int, line.split())
        adj[a].append(b)
        adj[b].append(a)
nA = n // 2  # sides: 0..nA-1 (A), nA..n-1 (B)

def nb_walks(src, length):
    """counts of non-backtracking walks of given length from src, indexed by endpoint"""
    cur = {(src, -1): 1}
    for _ in range(length):
        nxt = Counter()
        for (x, prev), c in cur.items():
            for y in adj[x]:
                if y != prev:
                    nxt[(y, x)] += c
        cur = nxt
    tot = Counter()
    for (x, _), c in cur.items():
        tot[x] += c
    return tot

for src in (0, nA):
    side = range(0, nA) if src < nA else range(nA, n)
    w2 = nb_walks(src, 2)
    w4 = nb_walks(src, 4)
    same = [v for v in side if v != src]
    m = [w2.get(v, 0) + w4.get(v, 0) for v in same]
    print(f"source {'A' if src < nA else 'B'}={src}: same-side targets={len(same)}")
    print("  NB walks of length 2 or 4 per same-side target, histogram:",
          dict(sorted(Counter(m).items())[:12]), "...")
    print("  min =", min(m), " targets with >=2 walks:", sum(1 for x in m if x >= 2),
          " with exactly 1:", sum(1 for x in m if x == 1), " with 0:", sum(1 for x in m if x == 0))
    print("  mean walks =", round(sum(m) / len(m), 3))
