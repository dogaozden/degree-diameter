"""Make a levelled hexagon doubling regular: balance the sides by deleting twins, then add edges.

Input: an unbalanced bipartite graph of maximum degree DELTA (edge list "n [m]" then "u v" lines, or a record JSON).
1. Bipartition by BFS; the larger side is L, the smaller P.
2. Twin classes on L (equal neighbourhoods). Delete |L| - |P| vertices of L, never the last member of a class,
   spreading the deletions round-robin over the classes. Deleting a vertex that keeps a twin changes no distance
   between the remaining vertices, so the diameter stays.
3. Every vertex now has deficit DELTA - deg >= 0 and both sides have the same total deficit. Add a simple bipartite
   graph between deficient vertices with exactly those degrees and no edge already present (random pairing of stubs,
   conflicts repaired by swaps). Adding edges never increases a distance.
Output: plain edge list ("n" then "u v"), and a record JSON when n <= 20000.

python3 regularize.py IN DELTA OUT_PREFIX [seed]
"""
import json
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

src, DELTA, prefix = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)

if src.endswith('.json'):
    d = json.loads(Path(src).read_text())['output']
    n = int(d[0])
    E = np.array(d[1], dtype=np.int64)
else:
    with open(src) as fh:
        n = int(fh.readline().split()[0])
        E = np.fromfile(fh, dtype=np.int64, sep=' ').reshape(-1, 2)
print('read', n, 'vertices', len(E), 'edges', flush=True)

order = np.argsort(np.concatenate([E[:, 0], E[:, 1]]), kind='stable')
nbr_all = np.concatenate([E[:, 1], E[:, 0]])[order]
deg = np.bincount(np.concatenate([E[:, 0], E[:, 1]]), minlength=n)
off = np.concatenate([[0], np.cumsum(deg)])
assert deg.max() <= DELTA, deg.max()

# 2-colouring by BFS over frontiers
side = np.full(n, -1)
side[0] = 0
front = np.array([0])
while len(front):
    idx = np.concatenate([np.arange(off[u], off[u + 1]) for u in front])
    nb = np.unique(nbr_all[idx])
    src_side = side[front[0]]
    assert np.all(side[front] == src_side)
    bad = nb[side[nb] == src_side]
    assert len(bad) == 0, 'not bipartite'
    nb = nb[side[nb] == -1]
    side[nb] = 1 - src_side
    front = nb
assert np.all(side >= 0), 'not connected'
sizes = [int((side == 0).sum()), int((side == 1).sum())]
Ls = 0 if sizes[0] > sizes[1] else 1
r = abs(sizes[0] - sizes[1])
print('sides', sizes, 'excess', r, 'on side', Ls, flush=True)

# twin classes on the larger side
cls = defaultdict(list)
for u in np.nonzero(side == Ls)[0]:
    cls[tuple(sorted(nbr_all[off[u]:off[u + 1]].tolist()))].append(int(u))
classes = sorted((sorted(c) for c in cls.values() if len(c) > 1), key=lambda c: c[0])
print('twin classes on larger side by size:', dict(Counter(len(c) for c in classes)),
      'deletable', sum(len(c) - 1 for c in classes), flush=True)
dele = []
rnd = 1
while len(dele) < r:
    progress = False
    for c in classes:
        if len(c) > rnd and len(dele) < r:
            dele.append(c[-rnd])
            progress = True
    assert progress, 'not enough twins'
    rnd += 1
dele = np.array(sorted(dele))
alive = np.ones(n, bool)
alive[dele] = False
keepE = alive[E[:, 0]] & alive[E[:, 1]]
E2 = E[keepE]
new_id = np.cumsum(alive) - 1
E2 = new_id[E2]
side2 = side[alive]
n2 = int(alive.sum())
deg2 = np.bincount(E2.ravel(), minlength=n2)
defi = DELTA - deg2
print('after deleting', len(dele), ': n', n2, 'sides', int((side2 == 0).sum()), int((side2 == 1).sum()),
      'deficit histogram', dict(Counter(defi.tolist())), flush=True)
assert defi.min() >= 0
X = [u for u in np.nonzero(side2 == 0)[0].tolist() for _ in range(defi[u])]
Y = [u for u in np.nonzero(side2 == 1)[0].tolist() for _ in range(defi[u])]
assert len(X) == len(Y), (len(X), len(Y))
defset = set(np.nonzero(defi > 0)[0].tolist())
mask = np.isin(E2[:, 0], list(defset)) & np.isin(E2[:, 1], list(defset))
old = set(map(tuple, np.sort(E2[mask], axis=1).tolist()))
rng.shuffle(Y)


def key(a, b):
    return (a, b) if a < b else (b, a)


cnt = Counter(key(X[i], Y[i]) for i in range(len(X)))


def bad(i):
    k = key(X[i], Y[i])
    return k in old or cnt[k] > 1


todo = [i for i in range(len(X)) if bad(i)]
tries = 0
while todo:
    i = todo.pop()
    if not bad(i):
        continue
    while True:
        tries += 1
        j = rng.randrange(len(X))
        ki, kj = key(X[i], Y[i]), key(X[j], Y[j])
        ni, nj = key(X[i], Y[j]), key(X[j], Y[i])
        if ni in old or nj in old or ni == nj or cnt[ni] > 0 or cnt[nj] > 0:
            continue
        cnt[ki] -= 1
        cnt[kj] -= 1
        cnt[ni] += 1
        cnt[nj] += 1
        Y[i], Y[j] = Y[j], Y[i]
        break
add = np.array([key(X[i], Y[i]) for i in range(len(X))], dtype=np.int64).reshape(-1, 2)
print('added', len(add), 'edges; repair swaps', tries, flush=True)
E3 = np.concatenate([E2, add])
deg3 = np.bincount(E3.ravel(), minlength=n2)
print('final n', n2, 'm', len(E3), 'degree histogram', dict(Counter(deg3.tolist())), flush=True)
txt = Path(prefix + '.txt')
with open(txt, 'w') as fh:
    fh.write(f'{n2}\n')
    np.savetxt(fh, E3, fmt='%d')
print('wrote', txt)
if n2 <= 20000:
    js = Path(prefix + '.json')
    js.write_text(json.dumps({'case': f'd{DELTA}D6', 'value': n2, 'output': [n2, E3.tolist()]}))
    print('wrote', js)
