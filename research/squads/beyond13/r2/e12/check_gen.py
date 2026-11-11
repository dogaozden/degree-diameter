#!/usr/bin/env python3
"""Independent diameter check of a Haar graph H(G,S), G = (meta or prod of two meta) x Z_n, from a haar_gen3
solution file ("d D meta m k r n NC N ..." or "d D prod meta m1 k1 r1 meta m2 k2 r2 n NC N ..", then d lines
"<idx> meta(a=A,j=J) z=Z" / "<idx> prod[meta(a=..,j=..);meta(a=..,j=..)] z=Z").
Own group law: (a,j)(b,l) = (a + r^j b mod m, j + l mod k) per factor; Z_n componentwise.
Vertices (g,A),(g,B); (g,A)~(s g,B). Right multiplication is a side-transitive automorphism, so BFS from (e,A) and
(e,B) each reaching all N vertices of both sides within D is exactly diameter <= D. Works in O(N d) with boolean
visited arrays only. Prints VALID / INVALID."""
import sys, re, time
import numpy as np
t0 = time.time()
L = open(sys.argv[1]).read().split('\n'); h = L[0].split()
d, D = int(h[0]), int(h[1])
ni = h.index('n'); ncyc = int(h[ni + 1]); N = int(h[h.index('N') + 1])
spec = h[2:ni]
if spec[0] == 'meta':
    facs = [tuple(map(int, spec[1:4]))]
else:
    assert spec[0] == 'prod'
    facs = [tuple(map(int, spec[2:5])), tuple(map(int, spec[6:9]))]
ords = [m * k for m, k, r in facs]
for m, k, r in facs:
    R = [pow(r, j, m) for j in range(k)]
    assert R[k - 1] * r % m == 1 % m, "r^k != 1"
Ntot = int(np.prod(ords)) * ncyc
assert Ntot == N, (Ntot, N)
Rs = [[pow(r, j, m) for j in range(k)] for m, k, r in facs]
def parse_elem(line):
    pairs = [tuple(map(int, p)) for p in re.findall(r'a=(\d+),j=(\d+)', line)]
    z = re.search(r'z=(\d+)', line); z = int(z.group(1)) if z else 0
    return pairs, z % ncyc
S = []
for line in L[1:1 + d]:
    pairs, z = parse_elem(line)
    assert len(pairs) == len(facs)
    S.append([v for (a, j), (m, k, r) in zip(pairs, facs) for v in (a % m, j % k)] + [z])
assert len(set(map(tuple, S))) == d and all(x == 0 for x in S[0]), "S0 must be e, gens distinct"
def mul_scalar_arr(s, comps):
    """s * g for a scalar element s (list of comps) and array comps (list of arrays), returns arrays."""
    out = []
    for i, (m, k, r) in enumerate(facs):
        a_g, j_g = comps[2 * i], comps[2 * i + 1]
        a_s, j_s = s[2 * i], s[2 * i + 1]
        out.append((a_s + Rs[i][j_s] * a_g) % m)
        out.append((j_s + j_g) % k)
    out.append((s[-1] + comps[-1]) % ncyc)
    return out
def inv(s):
    out = []
    for i, (m, k, r) in enumerate(facs):
        a_s, j_s = s[2 * i], s[2 * i + 1]
        jj = (-j_s) % k
        out.append((-Rs[i][jj] * a_s) % m); out.append(jj)
    out.append((-s[-1]) % ncyc)
    return out
def encode(comps):
    q = 0
    for i, (m, k, r) in enumerate(facs):
        x = comps[2 * i] * k + comps[2 * i + 1]
        q = q * ords[i] + x if i > 0 else x
    return q * ncyc + comps[-1]
def decode(idx):
    z = idx % ncyc; q = idx // ncyc
    comps = []
    xs = []
    for i in reversed(range(len(facs))):
        o = ords[i]; xs.append(q % o); q = q // o
    xs.reverse()
    for i, (m, k, r) in enumerate(facs):
        comps += [xs[i] // k, xs[i] % k]
    comps.append(z)
    return comps
# sanity: s * s^-1 = e for every generator (random group elements through encode/decode)
for s in S:
    si = inv(s)
    assert all(int(v[0]) == 0 for v in mul_scalar_arr(s, [np.array([v]) for v in si])), s
Sinv = [inv(s) for s in S]
def leftmul_idx(s, idx):
    comps = decode(idx)
    return encode(mul_scalar_arr(s, comps))
N_all = N
visA = np.zeros(N, dtype=bool); visB = np.zeros(N, dtype=bool)
def bfs(start_side):
    visA[:] = False; visB[:] = False
    e = 0
    if start_side == 'A': visA[e] = True; fA = np.array([e], dtype=np.int64); fB = np.zeros(0, dtype=np.int64)
    else: visB[e] = True; fB = np.array([e], dtype=np.int64); fA = np.zeros(0, dtype=np.int64)
    for lev in range(1, D + 1):
        candB = [leftmul_idx(s, fA) for s in S] if len(fA) else []
        candA = [leftmul_idx(si, fB) for si in Sinv] if len(fB) else []
        newB = np.unique(np.concatenate(candB)) if candB else np.zeros(0, dtype=np.int64)
        newA = np.unique(np.concatenate(candA)) if candA else np.zeros(0, dtype=np.int64)
        newB = newB[~visB[newB]]; newA = newA[~visA[newA]]
        visB[newB] = True; visA[newA] = True
        fA, fB = newA, newB
        if len(fA) == 0 and len(fB) == 0: break
    return int(visA.sum()), int(visB.sum())
resA = bfs('A'); print("from (e,A): reached A,B =", resA, "of", N, file=sys.stderr)
ok1 = resA == (N, N)
resB = bfs('B'); print("from (e,B): reached A,B =", resB, "of", N, file=sys.stderr)
ok2 = resB == (N, N)
print("VALID" if ok1 and ok2 else "INVALID", f"d={d} D={D} N={N} 2N={2*N} groups={spec} ncyc={ncyc} time={time.time()-t0:.1f}s")
