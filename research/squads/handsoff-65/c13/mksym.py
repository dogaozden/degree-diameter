# symmetric insertion of K vertex pairs into H684 = H(G,S), G = g342.txt (table), pi = left mult by g (order K)
# new pairs u_i (A side, id 684+2i), v_i (B side, id 685+2i); pi(u_i)=u_{i+1}, pi(v_i)=v_{i+1}
# usage: mksym.py K GELEM SEED OUTEDGES OUTPERM
import sys, random
tab = open('g342.txt').read().split()
m = int(tab[0]); T = [[int(tab[1 + i * m + j]) for j in range(m)] for i in range(m)]
K, g, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
random.seed(seed)
S = [106, 241, 112, 304, 137, 24]
base = [(x, m + T[x][s]) for x in range(m) for s in S]   # A_x ~ B_y, y = x*s
def piold(v):
    if v < m: return T[g][v]
    return m + T[g][v - m]
n = 2 * m + 2 * K
def pi(v):
    if v < 2 * m: return piold(v)
    i = (v - 2 * m) // 2; side = (v - 2 * m) % 2
    return 2 * m + 2 * ((i + 1) % K) + side
def orbit_edge(a, b):
    res = []; x, y = a, b
    for j in range(K):
        res.append((x, y)); x, y = pi(x), pi(y)
    return res
while True:
    reps = random.sample(base, 300)
    chosen = []; used_a = set(); used_b = set()
    for (a, b) in reps:
        orb = orbit_edge(a, b)
        As = {p[0] for p in orb}; Bs = {p[1] for p in orb}
        if As & used_a or Bs & used_b: continue
        chosen.append((a, b)); used_a |= As; used_b |= Bs
        if len(chosen) == 5: break
    if len(chosen) == 5: break
removed = set()
for (a, b) in chosen:
    for (x, y) in orbit_edge(a, b): removed.add((x, y))
E = [e for e in base if e not in removed]
for (a, b) in chosen:
    for j, (x, y) in enumerate(orbit_edge(a, b)):
        vj = 2 * m + 2 * j + 1; uj = 2 * m + 2 * j
        E.append((x, vj)); E.append((y, uj))
for i in range(K):
    E.append((2 * m + 2 * i, 2 * m + 2 * i + 1))
deg = [0] * n
for a, b in E: deg[a] += 1; deg[b] += 1
assert all(d == 6 for d in deg), set(deg)
assert len(set(E)) == len(E)
with open(sys.argv[4], 'w') as f:
    f.write(f"{n}\n")
    for a, b in E: f.write(f"{a} {b}\n")
with open(sys.argv[5], 'w') as f:
    f.write(" ".join(str(pi(v)) for v in range(n)) + "\n")
print("n", n, "edges", len(E), "K", K, "g", g)
