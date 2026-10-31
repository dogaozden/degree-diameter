# remove vertex pair (x in A, y in B, non-adjacent) from H684, remove 2 extra random edges, insert 2 pairs.
# labels: old A -> 0..340, new A u1=341,u2=342; old B -> 343..683, new B v1=684,v2=685; new pairs joined as K22.
# usage: mkpair.py SEED OUTEDGES
import sys, random
random.seed(int(sys.argv[1]))
tab = open('g342.txt').read().split()
m = int(tab[0]); T = [[int(tab[1 + i * m + j]) for j in range(m)] for i in range(m)]
S = [106, 241, 112, 304, 137, 24]
E0 = [(x, m + T[x][s]) for x in range(m) for s in S]
E0set = set(E0)
x = random.randrange(m); y = m + random.randrange(m)
while (x, y) in E0set: y = m + random.randrange(m)
rem = set(e for e in E0 if e[0] == x or e[1] == y)
rest = [e for e in E0 if e not in rem]
ext = []
for _ in range(2):
    e = random.choice(rest)
    while e[0] == x or e[1] == y: e = random.choice(rest)
    rest.remove(e); ext.append(e)
lab = {}
for i, a in enumerate([a for a in range(m) if a != x]): lab[a] = i
for i, b in enumerate([b for b in range(m, 2 * m) if b != y]): lab[b] = 343 + i
u1, u2, v1, v2 = 341, 342, 684, 685
n = 686
E = [(lab[a], lab[b]) for (a, b) in rest]
defA = [lab[a] for (a, b) in E0 if b == y] + [lab[a] for (a, b) in ext]
defB = [lab[b] for (a, b) in E0 if a == x] + [lab[b] for (a, b) in ext]
assert len(defA) == 8 and len(defB) == 8
random.shuffle(defA); random.shuffle(defB)
F = list(E)
for a in defA[:4]: F.append((a, v1))
for a in defA[4:]: F.append((a, v2))
for b in defB[:4]: F.append((u1, b))
for b in defB[4:]: F.append((u2, b))
F += [(u1, v1), (u1, v2), (u2, v1), (u2, v2)]
deg = [0] * n
for a, b in F: deg[a] += 1; deg[b] += 1
assert all(d == 6 for d in deg), set(deg)
assert len(set(F)) == len(F)
with open(sys.argv[2], 'w') as f:
    f.write(f"{n}\n")
    for a, b in F: f.write(f"{a} {b}\n")
print("n", n, "edges", len(F))
