# build 685 start: 684 Haar + new A-vertex u=684 adjacent to covering set S (6 B-vertices); each w in S drops one A-edge (w,z)
import sys, random
random.seed(int(sys.argv[1])); out = sys.argv[2]; mode = sys.argv[3] if len(sys.argv) > 3 else 'rand'
t = open('../c7/h684.edges').read().split(); n = int(t[0]); E = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
S = [int(x) for x in open('cover_S.txt').read().split()]
adj = {v: set() for v in range(n)}
for a, b in E: adj[a].add(b); adj[b].add(a)
col = {0: 0}; q = [0]
for x in q:
    for y in adj[x]:
        if y not in col: col[y] = 1 - col[x]; q.append(y)
E = set(tuple(sorted(e)) for e in E)
u = n
for w in S:
    zs = [z for z in adj[w] if col[z] == 0]
    z = random.choice(zs)
    E.discard(tuple(sorted((w, z))))
    E.add(tuple(sorted((w, u))))
with open(out, 'w') as f:
    f.write("%d\n" % (n + 1))
    for a, b in sorted(E): f.write("%d %d\n" % (a, b))
print("wrote", out, "edges", len(E))
