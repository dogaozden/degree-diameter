# mk_insert.py SEED OUT [pairs]: C168.1 plus `pairs` new (A,B) vertex pairs, each inserted by deleting 3 random edges
# x_i y_i and adding a ~ y1,y2,y3, b ~ x1,x2,x3 (degrees stay 3). Output: n = 168 + 2*pairs, A = 0..m-1, B = m..n-1.
import random, sys
seed = int(sys.argv[1]); out = sys.argv[2]; pairs = int(sys.argv[3]) if len(sys.argv) > 3 else 1
random.seed(seed)
L = open('/home/user/degree-diameter/research/squads/handsoff-37/shared/seeds/conder168.edges').read().split()
n0 = int(L[0]); E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
m0 = n0 // 2
E = [(a, b) for a, b in E]
# A side = 0..m0-1 (check)
assert all(a < m0 <= b for a, b in E), "not A-B with A=0..m0-1"
# relabel: new vertices appended: A: m0..m0+pairs-1, B: n0 + ... handled by shifting B indices
m = m0 + pairs; n = 2 * m
def Bmap(b): return b - m0 + m  # old B index (m0..n0-1) -> m + (b - m0)
E = [(a, Bmap(b)) for a, b in E]
newA = list(range(m0, m))
newB = list(range(n - pairs, n))
for k in range(pairs):
    a_new = newA[k]; b_new = newB[k]
    # choose 3 distinct edges among current edges, deleting them: their A endpoints x_i and B endpoints y_i
    idx = random.sample(range(len(E)), 3)
    # ensure distinct A endpoints and distinct B endpoints
    while len({E[i][0] for i in idx}) < 3 or len({E[i][1] for i in idx}) < 3:
        idx = random.sample(range(len(E)), 3)
    xs = [E[i][0] for i in idx]; ys = [E[i][1] for i in idx]
    E = [e for j, e in enumerate(E) if j not in idx]
    E += [(a_new, y) for y in ys] + [(x, b_new) for x in xs]
# remaining new A-B edges: none (a,b not adjacent)
assert len(E) == 3 * m, (len(E), 3*m)
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for a, b in E: f.write(f"{a} {b}\n")
print("wrote", out, "n", n, "edges", len(E))
