import json, itertools, numpy as np
q = 5
d = json.load(open('/home/user/degree-diameter/research/gh6/hex/hexagon_q5.json'))
print(list(d.keys())[:10])
P = []
for v in itertools.product(range(q), repeat=7):
    if next((c for c in v if c), 0) != 1: continue
    if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q: continue
    P.append(v)
pid = {p: i for i, p in enumerate(P)}
L = d['lines']
Ls = set(frozenset(l) for l in L)
print('points', len(P), 'lines', len(L), 'example line', L[0])
def normalize(v):
    for x in v:
        if x % q:
            s = pow(x, q - 2, q); return tuple((s * c) % q for c in v)
def inv3(a):
    det = (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1]) - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0]) + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])) % q
    di = pow(det, q - 2, q)
    adj = [[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m = [[a[r][c] for c in range(3) if c != i] for r in range(3) if r != j]
            adj[i][j] = ((-1) ** (i + j)) * (m[0][0]*m[1][1]-m[0][1]*m[1][0])
    return [[(adj[i][j] * di) % q for j in range(3)] for i in range(3)], det
rng = np.random.default_rng(3)
ok = 0; tot = 0
for t in range(5):
    while True:
        g = [[int(x) for x in row] for row in rng.integers(0, q, (3, 3))]
        gi, det = inv3(g)
        if det % q == 1: break
    gt = [[gi[j][i] for j in range(3)] for i in range(3)]
    def act(v):
        a = [sum(g[i][k] * v[k] for k in range(3)) % q for i in range(3)]
        b = [sum(gt[i][k] * v[4 + k] for k in range(3)) % q for i in range(3)]
        return normalize(tuple(a + [v[3]] + b))
    pp = [pid[act(p)] for p in P]
    img = [frozenset(pp[x] for x in l) for l in L]
    tot += 1; ok += all(s in Ls for s in img)
print('gh6 H(5): naive block SL3 preserves lines in', ok, 'of', tot, 'random tests')
