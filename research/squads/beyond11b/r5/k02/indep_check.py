# independent check: Haar graph H(G,S), G = Z_731 x|_7 Z_48 (r = 7), S from o731r7_9.txt
from collections import deque
m, k, r = 731, 48, 7
R = [pow(r, j, m) for j in range(k)]
def mul(x, y):  # (a1,j1)(a2,j2) = (a1 + r^j1 a2, j1+j2)
    a1, j1 = x; a2, j2 = y
    return ((a1 + R[j1] * a2) % m, (j1 + j2) % k)
S = []
for line in open('/home/user/degree-diameter/research/squads/beyond11b/r5/k02/o731r7_9.txt').read().split('\n')[1:]:
    if not line.strip(): continue
    idx = int(line.split()[0])
    S.append((idx // k, idx % k))
assert len(S) == 4
els = [(a, j) for a in range(m) for j in range(k)]
e = (0, 0)
def ecc(side):
    # vertices (g,0)=A side, (g,1)=B side; edges (g,A)~(s g,B) for s in S
    start = (e, side)
    dist = {start: 0}; q = deque([start])
    adj_cache = {}
    while q:
        v = q.popleft(); g, t = v
        if t == 0:
            nbrs = [(mul(s, g), 1) for s in S]
        else:
            # inverse edges: (g,B) ~ (s^-1 g, A)
            nbrs = []
            for s in S:
                si = None
                # inverse of s
                a, j = s
                inv_j = (-j) % k
                si = ((-R[inv_j] * a) % m, inv_j)  # check below
                nbrs.append((mul(si, g), 0))
        for w in nbrs:
            if w not in dist:
                dist[w] = dist[v] + 1; q.append(w)
    return dist
# verify inverse formula
for s in S:
    assert mul(s, ((-R[(-s[1]) % k] * s[0]) % m, (-s[1]) % k)) == e
dA = ecc(0); dB = ecc(1)
print("vertices reached", len(dA), len(dB), "of", 2 * m * k)
print("ecc A", max(dA.values()), "ecc B", max(dB.values()))
print("diameter <= 12:", max(dA.values()) <= 12 and max(dB.values()) <= 12 and len(dA) == 2*m*k and len(dB)==2*m*k)
