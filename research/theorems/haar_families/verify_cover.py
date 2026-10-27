"""Independent check of a Haar graph given as generator lines "a b c d z" over PGL(2,q) x Z_m (Python arithmetic only;
no code shared with haar_ecc.c).  Builds the component of (I,0,A) by BFS, then computes the eccentricity of (I,0,A) and
of the B-vertex (s_0, z_0, B).  Right translations by the A-side group of the component act transitively on each side
of the component (HAAR_FAMILIES.md, Lemma 2.6), so the larger eccentricity is the diameter of the component.
Usage: python3 verify_cover.py q m < gens"""
import sys
from collections import deque
q, m = int(sys.argv[1]), int(sys.argv[2])
gens = [tuple(int(t) for t in L.split()) for L in sys.stdin if L.strip()]
inv = [0] + [pow(a, q - 2, q) for a in range(1, q)]
def norm(a, b, c, d):
    a, b, c, d = a % q, b % q, c % q, d % q
    t = inv[a] if a else inv[b]
    return (a * t % q, b * t % q, c * t % q, d * t % q)
M = [(norm(a, b, c, d), z % m) for a, b, c, d, z in gens]
Minv = [((X[3], -X[1] % q, -X[2] % q, X[0]), z) for X, z in M]
def mul(X, Y):
    a, b, c, d = X; e, f, g, h = Y
    return norm(a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)
def nbrs(v):
    X, z, side = v
    if side == 0: return [(mul(Y, X), (z + t) % m, 1) for Y, t in M]
    return [(mul(Y, X), (z - t) % m, 0) for Y, t in Minv]
def bfs(src):
    dist = {src: 0}; dq = deque([src])
    while dq:
        v = dq.popleft()
        for w in nbrs(v):
            if w not in dist: dist[w] = dist[v] + 1; dq.append(w)
    return dist
I = norm(1, 0, 0, 1)
dA = bfs((I, 0, 0))
b0 = (M[0][0], M[0][1], 1)
dB = bfs(b0)
nA = sum(1 for v in dA if v[2] == 0); nB = sum(1 for v in dA if v[2] == 1)
print(f"component vertices {len(dA)} (A {nA}, B {nB}); same component from (s0,B): {len(dB) == len(dA) and b0 in dA}")
print(f"ecc(I,0,A) = {max(dA.values())}, ecc(s0,z0,B) = {max(dB.values())}, diameter = {max(max(dA.values()), max(dB.values()))}")
