# Audit items (4) Lemma 2.5(c), (5) Prop 4.1, plus Sec 1.2 counts, Lemma 3.1, Theorem 3.2 (own arithmetic only).
import itertools, random, math, sys
import qlib as L
random.seed(7)
disc = []
def check(name, cond, detail=""):
    if not cond:
        disc.append(name); print("FAIL", name, detail)
    return cond
def L0(p, q):
    L_ = 0
    while not (2 * p**(L_ // 2) > q*q): L_ += 2
    return L_

# ---- Sec 1.2 counts
for q in [3, 5, 7]:
    allpts = set(); quad = 0; ns = 0; nonsq_ps = 0
    for X in itertools.product(range(q), repeat=4):
        if X == (0,0,0,0): continue
        P = L.pnorm(X, q); allpts.add(P)
    pg = len(allpts)
    for P in allpts:
        a,b,c,d = P
        if (a*d - b*c) % q == 0: quad += 1
    pgl = pg - quad
    psl = sum(1 for P in allpts if (P[0]*P[3]-P[1]*P[2]) % q and L.is_square_mod(P[0]*P[3]-P[1]*P[2], q))
    check("PG(3,q) count", pg == (q+1)*(q*q+1), (q,pg))
    check("quadric (q+1)^2", quad == (q+1)**2, (q,quad))
    check("PGL = q(q^2-1)", pgl == q*(q*q-1), (q,pgl))
    check("PSL = q(q^2-1)/2", psl == q*(q*q-1)//2, (q,psl))
print("Sec 1.2 counts done")

# ---- Lemma 3.1 walk values (random walks, p in {3,5,7,13})
for p in [3, 5, 7, 13]:
    S = L.lps_set(p)
    for q in [r for r in L.primes(p+1, 40)][:3]:
        x, y = L.xy_solutions(q)[0]
        Sm = [L.psi(a, x, y, q) for a in S]
        for _ in range(300):
            Lw = 2 * random.randint(1, 4)
            idx = [random.randrange(len(S)) for _ in range(Lw)]
            # walk: step 1 A->B with M_1; step 2 B->A with adj(M_2); ...
            g = L.pnorm((1,0,0,1), q)
            for t, i in enumerate(idx):
                M = Sm[i] if t % 2 == 0 else L.madj(Sm[i], q)
                g = L.pnorm(L.mm(M, g, q), q)
            beta = (1,0,0,0)
            for t, i in enumerate(idx):
                al = S[i]
                # beta = conj(alpha_L) alpha_{L-1} conj(alpha_{L-2}) ... alpha_1 ; alpha_1 is idx[0]
                pass
            # build beta from the right: beta = abar_L a_{L-1} ... abar_2 a_1 (1-based)
            beta = (1,0,0,0)
            for t in range(Lw):   # t=0 is alpha_1
                al = S[idx[t]]
                fac = al if (t % 2 == 0) else L.qconj(al)
                beta = L.qmul(fac, beta)
            check("Lemma3.1 endpoint = psi(beta)", L.pnorm(L.psi(beta, x, y, q), q) == g, (p,q,idx))
            check("Lemma3.1 N(beta)=p^L", L.qnorm(beta) == p**Lw, (p,q,Lw))
            if p % 4 == 1:
                ok = beta[0] % 2 == 1 and all(t % 2 == 0 for t in beta[1:])
            else:
                ok = beta[0] % 2 == 1 and all(t % 2 == 0 for t in beta[1:])
            check("Lemma3.1 beta = 1 mod 2H", ok, (p,q,beta))
print("Lemma 3.1 done")

# ---- Theorem 3.2 (a),(b), and 3.5 (distance to psi(j), psi(k) too), Cor 3.3 inequality
rows32 = []
for p in [3, 5, 7, 13]:
    S = L.lps_set(p)
    for q in [r for r in L.primes(p+1, 41)]:
        for x, y in L.xy_solutions(q)[:1]:
            Sm = [L.psi(a, x, y, q) for a in S]
            d = L.haar_component(Sm, q)
            l0 = L0(p, q)
            for name, e in [("i", (1,0,0,0)), ("j", (0,1,0,0)), ("k", (0,0,1,0))]:
                # psi(i) etc: note psi of basis elements of H(Z) is psi((0,1,0,0)) for i
                pass
            Ai = L.psi((0,1,0,0), x, y, q); Aj = L.psi((0,0,1,0), x, y, q); Ak = L.psi((0,0,0,1), x, y, q)
            dist = {nm: d.get((L.pnorm(M, q), 'A')) for nm, M in [("i", Ai), ("j", Aj), ("k", Ak)]}
            for nm, dd in dist.items():
                check("Thm3.2a d>=L0 (%s)" % nm, dd is None or dd >= l0, (p,q,nm,dd,l0))
                if p % 4 == 1:
                    check("Thm3.2b equality (%s)" % nm, dd == l0, (p,q,nm,dd,l0))
            n = q*(q*q-1)
            rows32.append((p, q, l0, dist["i"], dist["j"], dist["k"], len(d), L.ecc(d)))
            # Cor 3.3: L0 >= 4 log_p q - 2 log_p 2 > (4/3) log_p n - 2 log_p 2
            check("Cor3.3 L0 bound", l0 >= 4*math.log(q, p) - 2*math.log(2, p) - 1e-12, (p,q))
            check("Cor3.3 second", 4*math.log(q,p) - 2*math.log(2,p) > (4/3)*math.log(n,p) - 2*math.log(2,p) - 1e-12, (p,q))
for r in rows32: print("p=%d q=%d L0=%d d(i)=%s d(j)=%s d(k)=%s comp=%d ecc(I,A)=%d" % r)
print("Thm 3.2 done")
print("DISCREPANCIES (b-part1):", len(disc))
