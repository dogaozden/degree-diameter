# checkgq.py: check that a baselift base file is W(q) flags + exactly two point->line perfect matchings.
import sys; sys.path.insert(0, '/home/user/degree-diameter/research/d16D8'); import gq
fn, q = sys.argv[1], int(sys.argv[2])
G = gq.load(q); N = G['N']
f = open(fn); V, m, E = map(int, f.readline().split())
flags = set((p, N + l) for l, L in enumerate(G['lines']) for p in L)
seen = set(); ext = []
for _ in range(E):
    x, y, c, cl = map(int, f.readline().split())
    if x > y: x, y = y, x
    if (x, y) in flags and (x, y) not in seen: seen.add((x, y))
    else: ext.append((x, y))
deg = [0] * (2 * N)
for x, y in ext: deg[x] += 1; deg[y] += 1
ok = V == 2 * N and len(seen) == len(flags) and set(deg) == {2} and all(x < N <= y for x, y in ext)
print('V', V, 'm', m, 'flags', len(seen), '/', len(flags), 'extra', len(ext), 'extra-degree set', set(deg), 'OK' if ok else 'BAD')
