# grow.py IN OUT k seed: add k pairs of new vertices (A*, B*) by edge insertion; keeps cubic bipartite.
# labels in OUT: A = 0..h'-1, B = h'..n'-1 (h' = h + k). Old A keep their index; old B index j -> h'+j.
import sys, random
inp, out, k, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
t = open(inp).read().split()
n = int(t[0]); h = n // 2
E = []
for i in range(3 * h):
    u, v = int(t[1 + 2 * i]), int(t[2 + 2 * i])
    a, b = (u, v) if u < h else (v, u)
    E.append((a, b - h))                       # B local index 0..h-1
newA = []; newB = []                           # new edges (A local, B local) using new ids
nA = h; nB = h                                 # new ids: A = h+t, B = h+t (local)
extra = []
for t_ in range(k):
    i = random.randrange(len(E)); j = random.randrange(len(E))
    while j == i or E[i][0] == E[j][0] or E[i][1] == E[j][1]:
        j = random.randrange(len(E))
    a1, b1 = E[i]; a2, b2 = E[j]
    # i=(a1,b1), j=(a2,b2) become (a1, B*), (a2, B*) ; new A* adj b1, b2 and B*
    E[i] = (a1, nB); E[j] = (a2, nB)
    extra.append((nA, b1)); extra.append((nA, b2)); extra.append((nA, nB))
    nA += 1; nB += 1
H = nA
with open(out, 'w') as f:
    f.write(f"{2*H}\n")
    for a, b in E + extra:
        f.write(f"{a} {H + b}\n")
