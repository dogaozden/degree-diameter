# insert.py SEED IN16 OUT17 : lift a cubic bipartite 16+16 controller to 17+17 by rewiring 3 edges
# (a1b1,a2b2,a3b3 -> new a* ~ b1,b2,b3 and new b* ~ a1,a2,a3). Old B vertex v (>= 16) becomes v+1; new A = 16, new B = 33.
import sys, random
seed, src, dst = int(sys.argv[1]), sys.argv[2], sys.argv[3]
random.seed(seed)
L = open(src).read().split('\n'); m = int(L[0]) // 2
E = [tuple(map(int, l.split())) for l in L[1:] if l.strip()]
E = [(u, v) for (u, v) in E if u < m]
while True:
    trip = random.sample(E, 3)
    if len({a for a, _ in trip}) == 3 and len({b for _, b in trip}) == 3: break
rest = [e for e in E if e not in trip]
mp = lambda v: v if v < m else v + 1
edges = [(a, mp(b)) for a, b in rest] + [(16, mp(b)) for _, b in trip] + [(a, 33) for a, _ in trip]
with open(dst, 'w') as f:
    f.write("34\n")
    for a, b in edges: f.write(f"{a} {b}\n")
