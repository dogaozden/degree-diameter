"""Check a mixed freed set (Lemma 3 of THEOREM.md) and build the 3-level graph X_1(H(q), sigma, R, NS).
Input: PAIRS file, lines "r s" (point id r of R, line id s = tau(r) of S), hexgen2 indexing.
Checks: R non-collinear, S non-concurrent, d(r,r') = d(s,s') in {4,6}, midpoint -> midline map well defined and
injective. Then builds sigma as in the proof of Lemma 3 and verifies (R2) directly, picks a random bipartite hub
graph of degree q-1 with same-side distances <= 6 for opposite owners, and writes the edge list for apsp.
usage: python3 mixbuild.py q PAIRS OUT.edges [seed]"""
import sys, struct, random, collections
q = int(sys.argv[1]); pairs = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
out = sys.argv[3]; rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
b = open('/home/user/degree-diameter/research/projects/hexagon-family/hex/hex_q%d.bin' % q, 'rb').read()
_, N, L = struct.unpack('3i', b[:12]); Q1 = q + 1
LP = [list(struct.unpack('%di' % Q1, b[12 + 4 * Q1 * l: 12 + 4 * Q1 * (l + 1)])) for l in range(L)]
PL = [[] for _ in range(N)]
for l in range(L):
    for p in LP[l]: PL[p].append(l)
def nbrs(v):  # incidence graph: points 0..N-1, lines N..2N-1
    return [N + l for l in PL[v]] if v < N else LP[v - N]
def bfs(src, maxd=6):
    d = {src: 0}; dq = collections.deque([src])
    while dq:
        v = dq.popleft()
        if d[v] >= maxd: continue
        for w in nbrs(v):
            if w not in d: d[w] = d[v] + 1; dq.append(w)
    return d
R = [r for r, s in pairs]; S = [s for r, s in pairs]; k = len(R)
assert len(set(R)) == k and len(set(S)) == k
dR = [bfs(r) for r in R]; dS = [bfs(N + s) for s in S]
mu = {}; muinv = {}
for i in range(k):
    for j in range(i + 1, k):
        a = dR[i][R[j]]; c = dS[i][N + S[j]]
        assert a in (4, 6), ('R distance', i, j, a)
        assert a == c, ('distance mismatch', i, j, a, c)
        if a == 4:
            m = [z for z in range(N) if dR[i].get(z) == 2 and dR[j].get(z) == 2]
            M = [l for l in range(L) if dS[i].get(N + l) == 2 and dS[j].get(N + l) == 2]
            assert len(m) == 1 and len(M) == 1
            m, M = m[0], M[0]
            assert mu.get(m, M) == M and muinv.get(M, m) == m, ('midpoint map inconsistent', i, j)
            mu[m] = M; muinv[M] = m
print('Lemma 3 conditions hold: |R| = %d, distance-4 pairs give %d midpoints' % (k, len(mu)))
# build sigma
sig = [-1] * N; used = [False] * L
def setsig(p, l):
    assert sig[p] in (-1, l) and (not used[l] or sig[p] == l), ('sigma clash', p, l)
    sig[p] = l; used[l] = True
for r, s in pairs: setsig(r, s)
for m, M in mu.items(): setsig(m, M)
for i in range(k):
    G2p = [z for z in range(N) if dR[i].get(z) == 2]; G2l = [l for l in range(L) if dS[i].get(N + l) == 2]
    restp = [z for z in G2p if sig[z] < 0]; restl = [l for l in G2l if not used[l]]
    assert len(restp) == len(restl), ('ball counts', i)
    rng.shuffle(restl)
    for z, l in zip(restp, restl): setsig(z, l)
fp = [p for p in range(N) if sig[p] < 0]; fl = [l for l in range(L) if not used[l]]; rng.shuffle(fl)
for p, l in zip(fp, fl): setsig(p, l)
assert all(x >= 0 for x in sig)
for i in range(k):   # (R2) directly
    A = set(sig[z] for z in range(N) if dR[i].get(z) == 2); B = set(l for l in range(L) if dS[i].get(N + l) == 2)
    assert A == B, ('R2 fails at', i)
print('sigma built, (R2) verified at every freed point')
Rset = set(R)
# hub graph: line-side hubs v_i ~ (R[i], lev), point-side u_i ~ (S[i], lev); random (q-1)-regular bipartite
opp = [[dR[i][R[j]] == 6 for j in range(k)] for i in range(k)]
def hub_ok(E):
    adjV = [[] for _ in range(k)]; adjU = [[] for _ in range(k)]
    for a, c in E: adjV[a].append(c); adjU[c].append(a)
    for side, A1, A2 in ((0, adjV, adjU), (1, adjU, adjV)):
        for i in range(k):
            dist = {i: 0}; fr = [i]
            for step in range(3):
                nf = []
                for x in fr:
                    for y in A1[x]:
                        for z in A2[y]:
                            if z not in dist: dist[z] = dist[x] + 2; nf.append(z)
                fr = nf
            for j in range(k):
                if j != i and opp[i][j] and j not in dist: return False
    return True
deg = min(q - 1, k)
import itertools, os
H = int(os.environ.get('NHUB', k))   # freed points that get hubs (the first H of the file); the others own none
if H < k:
    k_all = k; k = H
    opp = [row[:H] for row in opp[:H]]
found = None
for D in itertools.combinations(range(k), deg):   # circulant v_a ~ u_(a+d)
    if 0 not in D: continue
    Ec = set((a, (a + d) % k) for a in range(k) for d in D)
    if hub_ok(Ec): found = Ec; break
for attempt in range(0 if found else 200):
    E = set()
    for t in range(deg):
        perm = list(range(k)); rng.shuffle(perm)
        for a in range(k): E.add((a, perm[a]))
    if hub_ok(E): break
else:
    if not found: raise SystemExit('no hub graph found')
if found: E = found
deg_v = collections.Counter(a for a, c in E); deg_u = collections.Counter(c for a, c in E)
assert max(deg_v.values()) <= q - 1 and max(deg_u.values()) <= q - 1
n = 6 * N + 2 * k
def VP(p, i): return i * 2 * N + p
def VL(l, i): return i * 2 * N + N + l
edges = []
for i in range(3):
    for l in range(L):
        for p in LP[l]: edges.append((VP(p, i), VL(l, i)))
    for p in range(N):
        if p not in Rset: edges.append((VP(p, i), VL(sig[p], (i + 1) % 3)))
for t in range(k):
    for i in range(3):
        edges.append((6 * N + t, VP(R[t], i))); edges.append((6 * N + k + t, VL(S[t], i)))
for a, c in E: edges.append((6 * N + a, 6 * N + k + c))
with open(out, 'w') as f:
    f.write('%d\n' % n); f.write('\n'.join('%d %d' % e for e in edges) + '\n')
print('wrote', out, 'n =', n, 'edges =', len(edges))
