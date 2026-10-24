# build the base K=13 graph with some hub-graph edges removed and point-side super-hubs attached to line-hubs
# usage: mksuper.py OUT SEED "D1,D2,..." [SUPER2 "E1,..." ...]   (each removed HG edge is chosen at random per line-hub)
import sys, random
N = 3906; K = 13
out, seed = sys.argv[1], int(sys.argv[2]); supers = [list(map(int, s.split(','))) for s in sys.argv[3:]]
rnd = random.Random(seed)
lines = open('e_base13.txt').read().split('\n')
n0 = int(lines[0]); edges = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
hgE = [(a, b) for (a, b) in edges if a >= 6*N and b >= 6*N and a < 6*N+K and b >= 6*N+K and b < 6*N+2*K]
used_line = set()
for D in supers:
    for j in D:
        if j not in used_line: used_line.add(j)
remove = set()
# remove one hub-graph edge per line-hub used by a super-hub (its first available choice, random order)
for j in sorted(used_line):
    cand = [e for e in hgE if e[0] == 6*N+j and e not in remove]
    rnd.shuffle(cand)
    if cand: remove.add(cand[0])
edges2 = [e for e in edges if e not in remove]
n = n0 + len(supers)
for s, D in enumerate(supers):
    S = 6*N + 2*K + s
    for j in D: edges2.append((S, 6*N + j))
with open(out, 'w') as f:
    f.write('%d\n' % n)
    for a, b in edges2: f.write('%d %d\n' % (a, b))
print('wrote', out, 'n =', n, 'edges =', len(edges2), 'removed HG edges =', len(remove))
