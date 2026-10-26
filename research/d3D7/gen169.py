"""Start graph for the n = 169 case: a perfect depth-6 tree around a degree-2 vertex x (frozen), 64 leaves (A side),
42 outer B vertices, and random leaf-outer edges (free): 62 leaves get 2 outer edges, the two leaves given as
arguments get 1 (they are the other degree-2 vertices), every outer vertex gets 3.
Usage: python3 gen169.py seed y1 y2 > start.fz   (y1, y2 in 0..63, leaf indices)"""
import random, sys
seed, y1, y2 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
random.seed(seed)
edges = []
levels = [[0]]; nxt = 1
for d in range(1, 7):
    lev = []
    for p in levels[-1]:
        for _ in range(2):
            lev.append(nxt); edges.append((p, nxt, 1)); nxt += 1
    levels.append(lev)
leaves = levels[6]
outer = list(range(nxt, nxt + 42)); n = nxt + 42
stubs = []
for i, l in enumerate(leaves):
    stubs += [l] * (1 if i in (y1, y2) else 2)
assert len(stubs) == 126
while True:
    random.shuffle(stubs)
    pairs = [(stubs[3 * k + j], outer[k]) for k in range(42) for j in range(3)]
    if len(set(pairs)) == len(pairs):
        break
print(n)
for u, v, f in edges:
    print(u, v, f)
for u, v in pairs:
    print(u, v, 0)
