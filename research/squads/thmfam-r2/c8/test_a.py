# Audit items (1), (2), (3) of HAAR_FAMILIES.md sections 1.2, 2, 3 (own arithmetic only).
import itertools, random
import qlib as L
random.seed(1)
Q = [5, 7, 11, 13, 17, 19, 23]
disc = []
def check(name, cond, detail=""):
    if not cond:
        disc.append(name)
        print("FAIL", name, detail)
    return cond

# ---- (1) Lemma 2.3 relations
for q in Q:
    for x, y in L.xy_solutions(q):
        I_ = L.psi((0,1,0,0), x, y, q); J = L.psi((0,0,1,0), x, y, q); K = L.psi((0,0,0,1), x, y, q)
        one = (1,0,0,1); m1 = (q-1,0,0,q-1)
        check("I_^2=-1", L.mm(I_,I_,q) == tuple(t % q for t in m1), (q,x,y))
        check("J^2=-1", L.mm(J,J,q) == tuple(t % q for t in m1), (q,x,y))
        check("K^2=-1", L.mm(K,K,q) == tuple(t % q for t in m1), (q,x,y))
        check("I_J=K", L.mm(I_,J,q) == K, (q,x,y))
        check("JK=I_", L.mm(J,K,q) == I_, (q,x,y))
        check("K I_=J", L.mm(K,I_,q) == J, (q,x,y))
        # displayed formula equals a0 I + a1 I_ + a2 J + a3 K
        for _ in range(30):
            al = tuple(random.randint(-9, 9) for _ in range(4))
            comb = tuple((al[0]*one[t] + al[1]*I_[t] + al[2]*J[t] + al[3]*K[t]) % q for t in range(4))
            check("psi linear", comb == L.psi(al, x, y, q), (q,x,y,al))
            # homomorphism, determinant, adjugate
            be = tuple(random.randint(-9, 9) for _ in range(4))
            check("psi multiplicative", L.mm(L.psi(al,x,y,q), L.psi(be,x,y,q), q) == L.psi(L.qmul(al,be), x, y, q), (q,x,y,al,be))
            Pa = L.psi(al, x, y, q)
            check("det=N", L.mdet(Pa, q) == L.qnorm(al) % q, (q,x,y,al))
            check("adj=psi(conj)", L.madj(Pa, q) == L.psi(L.qconj(al), x, y, q), (q,x,y,al))
        # kernel = qH(Z) on a box, and surjectivity onto M2(F_q) for q <= 7
        if q <= 7:
            imgs = set()
            for al in itertools.product(range(q), repeat=4):
                imgs.add(L.psi(al, x, y, q))
            check("psi onto M2", len(imgs) == q**4, (q, x, y, len(imgs)))
            for al in itertools.product(range(-q, q+1), repeat=4):
                zero = L.psi(al, x, y, q) == (0,0,0,0)
                check("kernel", zero == all(t % q == 0 for t in al), (q,x,y,al))
        break  # one (x,y) per q for the expensive parts; relations are checked for all (x,y) above only for first
    # relations for all solutions (cheap)
    for x, y in L.xy_solutions(q):
        for al in [(1,2,3,4),(0,1,1,1),(3,-1,2,-2)]:
            check("psi linear all xy", L.psi(al,x,y,q) == tuple((al[0]*L.psi((1,0,0,0),x,y,q)[t] + al[1]*L.psi((0,1,0,0),x,y,q)[t] + al[2]*L.psi((0,0,1,0),x,y,q)[t] + al[3]*L.psi((0,0,0,1),x,y,q)[t]) % q for t in range(4)))
print("(1) Lemma 2.3 relations done")

# Lemma 2.4 / set S_p
for p in [3, 5, 7, 11, 13, 17]:
    S = L.lps_set(p)
    check("|S_p|=p+1", len(S) == p+1, (p, len(S)))
    check("norms", all(L.qnorm(a) == p for a in S), p)
    # closed under conj up to sign
    Sset = set(S)
    check("conj or -conj in S", all((L.qconj(a) in Sset) or (tuple(-t for t in L.qconj(a)) in Sset) for a in S), p)
    for q in primes_ if False else [r for r in range(p+1, 60) if L.is_prime(r)]:
        for x, y in L.xy_solutions(q)[:3]:
            P = [L.psi(a, x, y, q) for a in S]
            pts = [L.pnorm(M, q) for M in P]
            check("Lemma2.4b distinct", len(set(pts)) == p+1, (p,q,x,y))
            inv = set(L.pnorm(L.madj(M,q), q) for M in P)
            check("Lemma2.4b inversion closed", inv == set(pts), (p,q,x,y))
            check("det psi = p mod q", all(L.mdet(M,q) == p % q for M in P), (p,q,x,y))
            # Lemma 2.5(a) coset
            check("Lemma2.5a coset", (L.is_square_mod(p,q)) == all(L.is_square_mod(L.mdet(M,q),q) for M in P), (p,q))
print("Lemma 2.4/2.5(a) done")

# ---- (2) Theorem 2.6
for q in [7, 11, 13, 17, 19, 23, 29]:
    for x, y in L.xy_solutions(q)[:4]:
        zeta = (1,1,1,1)
        h = L.psi(zeta, x, y, q)
        # explicit matrix of Example 2.8
        hex_ = ((1+x+y) % q, (1+x-y) % q, (-1+x-y) % q, (1-x-y) % q)
        check("Example2.8 h", h == hex_, (q,x,y,h,hex_))
        check("det h = 4", L.mdet(h,q) == 4 % q, (q,x,y))
        h3 = L.mm(L.mm(h,h,q),h,q)
        check("h^3 = -8I", h3 == ((-8)%q,0,0,(-8)%q), (q,x,y,h3))
        check("h not scalar", not (h[1]==0 and h[2]==0 and h[0]==h[3]), (q,x,y))
        hinv = L.minv(h, q)
        for al in [a for a in itertools.product(range(-2,3), repeat=4)]:
            lhs = L.mm(L.mm(h, L.psi(al,x,y,q), q), hinv, q)
            rhs = L.psi(L.sigma(al), x, y, q)
            check("Thm2.6b matrix conj", lhs == rhs, (q,x,y,al,lhs,rhs))
            if len(disc) > 50: break
        # quaternion identity zeta i zeta-bar = 4 j, zeta^-1 relation
        zb = L.qconj(zeta)
        check("zeta i zbar = 4j", L.qmul(L.qmul(zeta,(0,1,0,0)),zb) == (0,0,4,0), "")
# Example 2.8 p=5 cycle check
for q in [13, 17, 19, 23]:
    for x, y in L.xy_solutions(q)[:3]:
        h = L.psi((1,1,1,1), x, y, q); hinv = L.minv(h, q)
        for sgn in (1, -1):
            a = (1, 2*sgn, 0, 0); b = (1, 0, 2*sgn, 0); c = (1, 0, 0, 2*sgn)
            ca = L.mm(L.mm(h, L.psi(a,x,y,q), q), hinv, q)
            check("Ex2.8 1+2i->1+2j", ca == L.psi(b,x,y,q), (q,x,y,sgn))
            cb = L.mm(L.mm(h, L.psi(b,x,y,q), q), hinv, q)
            check("Ex2.8 1+2j->1+2k", cb == L.psi(c,x,y,q), (q,x,y,sgn))
            cc = L.mm(L.mm(h, L.psi(c,x,y,q), q), hinv, q)
            check("Ex2.8 1+2k->1+2i", cc == L.psi(a,x,y,q), (q,x,y,sgn))

# cycle types of conjugation by h on psi(S_p) (projectively)
for p in [3, 5, 7, 11, 13, 17, 19]:
    S = L.lps_set(p)
    for q in [q for q in [23, 29, 31, 37, 41, 43, 47] if q > p][:2] + [r for r in [7,11,13] if r > p][:1]:
        x, y = L.xy_solutions(q)[0]
        h = L.psi((1,1,1,1), x, y, q); hinv = L.minv(h, q)
        pts = {L.pnorm(L.psi(a,x,y,q),q): a for a in S}
        perm = {}
        for P, a in pts.items():
            Pc = L.pnorm(L.mm(L.mm(h, L.psi(a,x,y,q), q), hinv, q), q)
            check("Thm2.6c conj permutes", Pc in pts, (p,q))
            perm[P] = Pc
        # cycle type
        seen = set(); cyc = []
        for P in pts:
            if P in seen: continue
            n = 0; Q_ = P
            while Q_ not in seen:
                seen.add(Q_); Q_ = perm[Q_]; n += 1
            cyc.append(n)
        cyc.sort()
        fixed = cyc.count(1)
        check("Thm2.6c: fixed points are a1=a2=a3", fixed == sum(1 for a in S if a[1]==a[2]==a[3]), (p,q,cyc))
        expect = {3: [1,3], 5: [3,3], 7: [1,1,3,3], 11: [3,3,3,3], 13: [1,1,3,3,3,3], 17: [3]*6, 19: [1,1]+[3]*6}[p]
        check("Thm2.6c cycle type table", cyc == expect, (p,q,cyc,expect))
        # (Example 2.8 mention) fixed-point count predicted: 0 if p=2 mod 3; 2 if p=1 mod 3 (p>3); 1 if p=3
        pred = 1 if p == 3 else (0 if p % 3 == 2 else 2)
        check("fixed count prediction", fixed == pred, (p,q,fixed,pred))
print("(2) Theorem 2.6 done")

# ---- (3) Example 2.8 neighbourhood formulas, q=13 full check (and others)
def ex28_A(X, x, y, q):
    a, b, c, d = X
    out = []
    for s in (1, -1):   # s = + gives the first sign in each formula
        out.append(((1+s*2*x)*a - s*2*y*c, (1+s*2*x)*b - s*2*y*d, -s*2*y*a + (1-s*2*x)*c, -s*2*y*b + (1-s*2*x)*d))
        out.append((a + s*2*c, b + s*2*d, c - s*2*a, d - s*2*b))
        out.append(((1+s*2*y)*a + s*2*x*c, (1+s*2*y)*b + s*2*x*d, s*2*x*a + (1-s*2*y)*c, s*2*x*b + (1-s*2*y)*d))
    return set(L.pnorm(tuple(t % q for t in o), q) for o in out)
def ex28_B(Y, x, y, q):
    # the same six formulas with the signs (the ∓ rule): s -> -s
    a, b, c, d = Y
    out = []
    for s in (-1, 1):
        out.append(((1+s*2*x)*a - s*2*y*c, (1+s*2*x)*b - s*2*y*d, -s*2*y*a + (1-s*2*x)*c, -s*2*y*b + (1-s*2*x)*d))
        out.append((a + s*2*c, b + s*2*d, c - s*2*a, d - s*2*b))
        out.append(((1+s*2*y)*a + s*2*x*c, (1+s*2*y)*b + s*2*x*d, s*2*x*a + (1-s*2*y)*c, s*2*x*b + (1-s*2*y)*d))
    return set(L.pnorm(tuple(t % q for t in o), q) for o in out)
for q, (x, y) in [(13, (3, 4)), (13, (2, 3)), (11, (3, 1)), (17, L.xy_solutions(17)[0])]:
    if (x*x + y*y + 1) % q: print("NOTE: (x,y)=(%d,%d) does not satisfy x^2+y^2+1=0 mod %d; x^2+y^2+1 mod q = %d" % (x, y, q, (x*x+y*y+1) % q))
    S5 = [(1,2,0,0),(1,-2,0,0),(1,0,2,0),(1,0,-2,0),(1,0,0,2),(1,0,0,-2)]
    Ms = [L.psi(a, x, y, q) for a in S5]
    PGL = [X for X in itertools.product(range(q), repeat=4) if (X[0]*X[3]-X[1]*X[2]) % q]
    PGLn = sorted(set(L.pnorm(X, q) for X in PGL))
    bad = 0
    for X in PGLn:
        # generator-edge neighbours of (X,A)
        gen_nb = set(L.pnorm(L.mm(M, X, q), q) for M in Ms)
        if gen_nb != ex28_A(X, x, y, q) or len(gen_nb) != 6:
            bad += 1
        # generator-edge neighbours of (X,B): (adj(M) X, A)
        gen_nbB = set(L.pnorm(L.mm(L.madj(M,q), X, q), q) for M in Ms)
        if gen_nbB != ex28_B(X, x, y, q) or len(gen_nbB) != 6:
            bad += 1
    check("Ex2.8 neighbourhoods", bad == 0, (q, x, y, bad, len(PGLn)))
    print("Ex2.8 neighbour check q=%d (x,y)=(%d,%d): vertices %d, mismatches %d" % (q, x, y, len(PGLn), bad))
    # diameter of the graph on the component of (I,A) for this (x,y)
    Sm = Ms
    d = L.haar_component(Sm, q)
    nA = sum(1 for v in d if v[1]=='A'); nB = sum(1 for v in d if v[1]=='B')
    ecc_A = max(dd for vv, dd in d.items() if vv[1] == 'A' and False) if False else None
    e_IA = L.ecc(d)  # eccentricity of (I,A) in the component = max over all vertices
    print("   component of (I,A): size %d (A %d, B %d), ecc(I,A) in component = %d" % (len(d), nA, nB, e_IA))
print("(3) Example 2.8 done")
print("DISCREPANCIES (a):", len(disc))
for t in disc[:20]: print("  ", t)
