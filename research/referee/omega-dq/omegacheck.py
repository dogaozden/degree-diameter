"""omegacheck.py (referee omega-dq): second, independent build of Omega H_q in Python (vertex names are tuples, wiring
re-derived from Figs 2.21a/b by position: star edge between copies k-1 and k+1, circle arc between copies k+2 and k+3
in (a); circle arc between copies k+3 and k+4, star edge between copies k-1 and k+1 in (b)), reading 2 (K(t,k) on point
t, K(t,kbar) on line t), then a plain BFS. Prints eccentricity and distance counts of the source and the distance to a
given target.  usage: python3 omegacheck.py hex.txt types t k bar target_copy target_basevertex"""
import sys
from collections import deque
hexp, types = sys.argv[1], sys.argv[2]
t0, k0, b0, tc, tv = map(int, sys.argv[3:8])
with open(hexp) as f:
    nb = int(f.readline()); E = [tuple(map(int, l.split())) for l in f if l.strip()]
n1 = nb // 2
adj = {}
def link(x, y):
    adj.setdefault(x, []).append(y); adj.setdefault(y, []).append(x)
C = 5 * len(types)
for c in range(C):
    for u, v in E: link(('c', c, u), ('c', c, v))
for B, ty in enumerate(types):
    for k in range(5):
        if ty == 'a': star, arc = ('K', k, 0), ('K', k, 1)        # (a): k on the star, kbar on the arc
        else:         star, arc = ('K', k, 1), ('K', k, 0)        # (b): kbar on the star, k on the arc
        kk = k
        star_copies = [5 * B + (kk - 1) % 5, 5 * B + (kk + 1) % 5]
        arc_copies = [5 * B + (kk + 2) % 5, 5 * B + (kk + 3) % 5] if ty == 'a' else [5 * B + (kk + 3) % 5, 5 * B + (kk + 4) % 5]
        for (_, k_, bar), cs in ((star, star_copies), (arc, arc_copies)):
            for t in range(n1):
                base = t if bar == 0 else n1 + t                    # reading 2: k-sets on points, kbar-sets on lines
                for c in cs: link(('K', t, k_, bar), ('c', c, base))
N = len(adj)
degs = sorted(set(len(v) for v in adj.values()))
print(f"vertices {N}, edges {sum(len(v) for v in adj.values()) // 2}, degrees {degs}")
src = ('K', t0, k0, b0); dist = {src: 0}; dq = deque([src])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if y not in dist: dist[y] = dist[x] + 1; dq.append(y)
ecc = max(dist.values()); cnt = [0] * (ecc + 1)
for d in dist.values(): cnt[d] += 1
print(f"source {src}: reached {len(dist)} of {N}, eccentricity {ecc}, counts {cnt}")
print(f"distance to ('c', {tc}, {tv}) = {dist[('c', tc, tv)]}")
