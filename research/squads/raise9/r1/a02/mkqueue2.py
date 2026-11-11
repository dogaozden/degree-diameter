import math, itertools
out = []
# (a) semidirect Z_p^2 x| Z_k, generator matrix M in GL2(p) with M^k = I, deduped by conjugacy and power-equivalence
def gl2(p):
    return [m for m in itertools.product(range(p), repeat=4) if (m[0]*m[3]-m[1]*m[2]) % p]
def mul(p, A, B):
    a,b,c,d = A; e,f,g,h = B
    return ((a*e+b*g)%p, (a*f+b*h)%p, (c*e+d*g)%p, (c*f+d*h)%p)
def inv(p, A):
    a,b,c,d = A; det = (a*d-b*c)%p; di = pow(det, p-2, p)
    return ((d*di)%p, (-b*di)%p, (-c*di)%p, (a*di)%p)
for p in [2,3,5,7]:
    G = gl2(p); I = (1,0,0,1)
    # conjugacy class id
    cls = {}
    cid = 0
    for M in G:
        if M in cls: continue
        orb = {mul(p, mul(p, g, M), inv(p, g)) for g in G}
        for x in orb: cls[x] = cid
        cid += 1
    def order(M):
        x, o = M, 1
        while x != I:
            x = mul(p, x, M); o += 1
        return o
    for k in range(2, 400):
        N = p*p*k
        if N < 254 or N > 330: continue
        seen = set()
        for M in G:
            o = order(M)
            if k % o: continue
            key = min(cls[(lambda X: X)(tuple(__import__('functools').reduce(lambda A_, _: mul(p, A_, M), range(j-1), M)))] for j in range(1, k+1) if math.gcd(j, k) == 1) if False else None
            # powers of M^j for j coprime to k, class ids
            ids = []
            X = I
            for j in range(1, k+1):
                X = mul(p, X, M)
                if math.gcd(j, k) == 1: ids.append(cls[X])
            key = min(ids)
            if key in seen: continue
            seen.add(key)
            a,b,c,d = M
            out.append(f"semi {p} {k} {a} {b} {c} {d}")
# (b) products / non-metacyclic bases
for k in range(2, 400):
    pass
bases = {"sl2 3": 24, "perm 4 1,0,2,3 ; 1,2,3,0": 24, "perm 4 1,2,0,3 ; 1,0,3,2": 12, "psl2 5": 60, "heis 3": 27, "q8": 8}
for b, o in bases.items():
    for k in range(2, 400):
        if 254 <= o*k <= 330:
            out.append(f"{b} x cyc {k}")
for a in range(3, 42):
    for b in range(a, 42):
        if 254 <= 4*a*b <= 330:
            out.append(f"dih {a} x dih {b}")
open("queue2.txt", "w").write("\n".join(out) + "\n")
import collections
print(len(out), collections.Counter(s.split()[0] for s in out))
