# Builds the metacyclic group G = <a,b | a^N=1, b^Q=1, b a b^-1 = a^R>, elements (x,j) -> index x + N*j,
# computes Aut(G) by brute force over images (u,v) of (a,b) with full homomorphism check,
# computes Aut-orbits on non-identity elements, and writes a group file for the C search.
# usage: python3 setup_group.py N Q R outfile
import sys
import numpy as np

N, Q, R, outfile = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
assert pow(R, Q, N) == 1, "need R^Q = 1 mod N"
n = N * Q

def idx(x, j):
    return (x % N) + N * (j % Q)

def parts(g):
    return g % N, g // N

M = np.zeros((n, n), dtype=np.int64)
for g in range(n):
    x, j = parts(g)
    for h in range(n):
        y, k = parts(h)
        M[g, h] = idx(x + pow(R, j, N) * y, j + k)

e = idx(0, 0)
assert all(M[e, h] == h and M[h, e] == h for h in range(n))
assert all(M[M[g, h], k] == M[g, M[h, k]] for g in range(0, n, 7) for h in range(n) for k in range(0, n, 11))
inv = np.array([int(np.where(M[g] == e)[0][0]) for g in range(n)])

def power(g, t):
    r = e
    for _ in range(t):
        r = M[r, g]
    return r

def order(g):
    t, r = 1, g
    while r != e:
        r = M[r, g]
        t += 1
    return t

a = idx(1, 0)
b = idx(0, 1)
# check the defining relation b a b^-1 = a^R in G
assert M[M[b, a], inv[b]] == power(a, R)
ordN_elems = [g for g in range(n) if power(g, N) == e]
ordQ_elems = [g for g in range(n) if power(g, Q) == e]
powA = [power(a, x) for x in range(N)]
powB = [power(b, j) for j in range(Q)]
auts = []
for u in ordN_elems:
    pu = [e]
    for x in range(1, N):
        pu.append(M[pu[-1], u])
    powU_R = power(u, R)
    for v in ordQ_elems:
        # relation v u v^-1 = u^R
        if M[M[v, u], inv[v]] != powU_R:
            continue
        pv = [e]
        for j in range(1, Q):
            pv.append(M[pv[-1], v])
        phi = np.array([M[pu[x], pv[j]] for j in range(Q) for x in range(N)], dtype=np.int64)
        # phi(x,j) = u^x v^j with index x + N*j
        if len(set(phi.tolist())) != n:
            continue
        # full homomorphism check on all pairs
        if not np.array_equal(phi[M], M[np.ix_(phi, phi)]):
            continue
        auts.append(phi)
A = np.array(auts)
print("N,Q,R =", N, Q, R, " |G| =", n, " |Aut(G)| =", len(auts))
# orbits on non-identity elements
orb_id = -np.ones(n, dtype=np.int64)
orbits = []
for g in range(n):
    if g == e or orb_id[g] >= 0:
        continue
    orb = sorted(set(A[:, g].tolist()))
    for h in orb:
        orb_id[h] = len(orbits)
    orbits.append(orb)
orbits.sort(key=lambda o: (-len(o), o[0]))
for k in range(len(orbits)):
    for h in orbits[k]:
        orb_id[h] = k
print("orbit sizes (desc):", [len(o) for o in orbits])
# orbit-ordered iterations: iteration k uses rep r_k = min(orbit k), pool = non-identity elements in orbits >= k, minus rep
with open(outfile, "w") as f:
    f.write(f"{n}\n")
    for g in range(n):
        f.write(" ".join(str(int(M[g, h])) for h in range(n)) + "\n")
    f.write(f"{e}\n")
    f.write(f"{len(orbits)}\n")
    for k, orb in enumerate(orbits):
        rep = orb[0]
        pool = [h for kk in range(k, len(orbits)) for h in orbits[kk] if h != rep]
        f.write(f"{rep} {len(pool)} " + " ".join(map(str, pool)) + "\n")
print("wrote", outfile)
