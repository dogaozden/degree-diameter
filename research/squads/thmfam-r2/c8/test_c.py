# Audit item (4) Lemma 2.5(c) and item (5) Proposition 4.1 (own arithmetic only).
import random, sys
from collections import deque
import qlib as L
random.seed(11)
disc = []
def check(name, cond, detail=""):
    if not cond:
        disc.append(name); print("FAIL", name, detail)
    return cond
def L0(p, q):
    e = 0
    while not (2 * p**(e // 2) > q*q): e += 2
    return e

# ---- (4) Lemma 2.5(c): ecc(I,A) = ecc(c,B) for every c in psi(S_p); diam = ecc(I,A) for small q
rows4 = []
for p in [3, 5, 7, 13]:
    S = L.lps_set(p)
    for q in [r for r in L.primes(p+1, 37)]:
        x, y = L.xy_solutions(q)[0]
        Sm = [L.psi(a, x, y, q) for a in S]
        d = L.haar_component(Sm, q)
        eIA = L.ecc(d)
        eqs = []
        for a in S:
            c = L.pnorm(L.psi(a, x, y, q), q)
            dc = L.haar_component(Sm, q, start=(c, 'B'))
            check("Lemma2.5c comp(c,B)=comp(I,A)", set(dc) == set(d), (p,q,a))
            e_cB = L.ecc(dc)
            eqs.append(e_cB)
            check("Lemma2.5c ecc(c,B)=ecc(I,A)", e_cB == eIA, (p,q,a,e_cB,eIA))
        if q <= 13:
            # full diameter over all vertices (BFS from every vertex)
            verts = list(d.keys())
            diam = 0
            for v in verts:
                diam = max(diam, L.ecc(L.haar_component(Sm, q, start=v)))
            check("Lemma2.5c diam=ecc(I,A)", diam == eIA, (p,q,diam,eIA))
            rows4.append((p,q,len(d),eIA,diam))
        else:
            rows4.append((p,q,len(d),eIA,None))
for r in rows4: print("p=%d q=%d |Gamma|=%d ecc(I,A)=%d diam=%s" % r)
print("(4) done; discrepancies so far", len(disc))

# ---- (5) Proposition 4.1 on covers H(PGL(2,q) x Z_m, S~) with arbitrary kappa: S_p -> Z_m
def cover_dist_from_IA(Sm, labels, q, m):
    """BFS on PGL(2,q) x Z_m from (I,0,A). labels[t] = kappa(alpha_t) in Z_m. Convention of Lemma: (g,k,A)~(M g,k+t,B),
    (g,k,B) ~ (adj(M) g, k-t, A)."""
    I = L.pnorm((1,0,0,1), q)
    s = (I, 0, 'A'); dist = {s: 0}; dq = deque([s])
    adjs = [L.madj(M, q) for M in Sm]
    while dq:
        v = dq.popleft(); g, z, side = v
        if side == 'A':
            nxt = [(L.pnorm(L.mm(M, g, q), q), (z + t) % m, 'B') for M, t in zip(Sm, labels)]
        else:
            nxt = [(L.pnorm(L.mm(Mi, g, q), q), (z - t) % m, 'A') for Mi, t in zip(adjs, labels)]
        for w in nxt:
            if w not in dist:
                dist[w] = dist[v] + 1; dq.append(w)
    return dist
mins = []
for p in [3, 5, 7, 13]:
    S = L.lps_set(p)
    for q in [r for r in L.primes(p+1, 23)][:4]:
        x, y = L.xy_solutions(q)[0]
        Sm = [L.psi(a, x, y, q) for a in S]
        Pi = L.pnorm(L.psi((0,1,0,0), x, y, q), q)
        l0 = L0(p, q)
        for m in [2, 3, 4, 7]:
            for trial in range(3):
                labels = [random.randrange(m) for _ in S]
                dist = cover_dist_from_IA(Sm, labels, q, m)
                ds = [dist[(Pi, z, 'A')] for z in range(m) if (Pi, z, 'A') in dist]
                check("Prop4.1 d>=L0", all(dd >= l0 for dd in ds), (p,q,m,labels,min(ds) if ds else None,l0))
                if ds: mins.append((p,q,m,min(ds),l0,len(dist)))
# also: is the bound attained? (informational)
for r in mins[:25]: print("p=%d q=%d m=%d min_z d=%d L0=%d |comp|=%d" % r)
print("(5) done; discrepancies total", len(disc))
print("DISCREPANCIES (c):", len(disc))
