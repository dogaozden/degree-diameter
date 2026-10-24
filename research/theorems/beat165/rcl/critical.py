# For a controller in fitq format: the label words of length 4 that some same-side pair depends on, i.e. pairs
# (c, d) at distance 4 whose geodesic words form a small set, and vertices c whose closed reduced 4-walks are few.
# Prints, per such pair, the set of candidate words (a chart must make at least one word in each set nonsingular).
import sys, collections
lines = open(sys.argv[1]).read().split('\n')
n, nA = map(int, lines[0].split()); sa = list(map(int, lines[1].split())); sb = list(map(int, lines[2].split()))
sai = [0]*n; sbi = [0]*n
for i in range(n): sai[sa[i]] = i; sbi[sb[i]] = i
def step(t, v): return (sa, sai, sb, sbi)[t][v]
L = 'aAbB'
need = collections.Counter()
for c in range(n):
    dist = {c: 0}; frontier = [c]
    for dd in range(1, 5):
        nf = []
        for v in frontier:
            for t in range(4):
                w = step(t, v)
                if w not in dist: dist[w] = dd; nf.append(w)
        frontier = nf
    words = collections.defaultdict(set)
    for t1 in range(4):
        x1 = step(t1, c)
        for t2 in range(4):
            if t2 == t1 ^ 1: continue
            x2 = step(t2, x1)
            for t3 in range(4):
                if t3 == t2 ^ 1: continue
                x3 = step(t3, x2)
                for t4 in range(4):
                    if t4 == t3 ^ 1: continue
                    words[step(t4, x3)].add(L[t1] + L[t2] + L[t3] + L[t4])
    for d, dc in dist.items():
        if (d < nA) != (c < nA): continue
        if dc == 4 or d == c:
            key = tuple(sorted(words[d]))
            if len(key) <= 2: need[key] += 1
for key, cnt in sorted(need.items(), key=lambda x: -x[1]):
    print(cnt, ' '.join(key))
