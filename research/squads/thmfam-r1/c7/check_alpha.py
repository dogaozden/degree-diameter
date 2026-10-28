import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/thmfam-r1/c7')
from c7lib import *
def norm(M, q):
    a,b,c,d = [x % q for x in M]
    for x in (a,b,c,d):
        if x: inv = pow(x, q-2, q); return tuple(y*inv % q for y in (a,b,c,d))
def mul(A,B,q):
    a,b,c,d=A; e,f,g,h=B
    return ((a*e+b*g)%q,(a*f+b*h)%q,(c*e+d*g)%q,(c*f+d*h)%q)
def inv(A,q):
    a,b,c,d=A; det=(a*d-b*c)%q; di=pow(det,q-2,q)
    return ((d*di)%q,(-b*di)%q,(-c*di)%q,(a*di)%q)
def check(p,q):
    gens=parse(p,q); perm,cyc=orbits(gens)
    M=[norm(g[1],q) for g in gens]
    target=[norm(M[perm[i]],q) for i in range(len(gens))]
    for a,b,c,d in itertools.product(range(q),repeat=4):
        if (a*d-b*c)%q==0: continue
        G=(a,b,c,d); Gi=inv(G,q)
        if all(norm(mul(mul(G,M[i],q),Gi,q),q)==target[i] for i in range(len(gens))):
            return G
    return None
for p,q in [(7,11),(7,13),(13,17)]:
    print(p,q,'conjugator for shift:',check(p,q))
