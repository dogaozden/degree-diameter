# Lemma 4.3, enumerated independently. Six distinct singular points t,y1..y5 of Q(6,q).
# Aligned classes: the y's on one totally singular line through t (partition of {0..4}).
# Rich lines: maximal sets of >=3 y's on one PG line not through t; such a line meets each aligned class
# in <=1 point and two rich lines share <=1 point.
# Overlaps C_i = y_i^perp ∩ opp(t), |C_i| = q^4:
#   aligned pair -> 0; pair on a rich line l -> X_l >= q^3-q; other pair -> >= q^3-q;
#   triple with an aligned pair -> 0; triple inside a rich line -> X_l; other triple -> <= (q+1)^2.
# Upper bound on |U C_i|: Bonferroni S1-S2+S3; for a rich line of 5 points the exact 5q^4-4X_l.
from itertools import combinations
import sys
q=int(sys.argv[1]) if len(sys.argv)>1 else 7
m2=int(sys.argv[2]) if len(sys.argv)>2 else 140
Y=range(5)
def partitions(s):
    s=list(s)
    if not s: yield []; return
    f=s[0]
    for p in partitions(s[1:]):
        for i in range(len(p)):
            yield p[:i]+[[f]+p[i]]+p[i+1:]
        yield [[f]]+p
def rich_systems(cls):
    cl={y:i for i,c in enumerate(cls) for y in c}
    cands=[frozenset(S) for r in (3,4,5) for S in combinations(Y,r) if len({cl[y] for y in S})==r]
    out=[]
    def rec(i,chosen):
        if i==len(cands): out.append(list(chosen)); return
        rec(i+1,chosen)
        S=cands[i]
        if all(len(S&T)<=1 for T in chosen): rec(i+1,chosen+[S])
    rec(0,[])
    return out
L=q**3-q; T3=(q+1)**2
types={}
nlab=0
for cls in partitions(Y):
    cl={y:i for i,c in enumerate(cls) for y in c}
    for rich in rich_systems(cls):
        nlab+=1
        def aligned(a,b): return cl[a]==cl[b]
        def online(S): return [l for l in rich if set(S)<=l]
        if any(len(l)==5 for l in rich):
            U=5*q**4-4*L
        else:
            S1=5*q**4; S2lo=0; S3hi=0
            for a,b in combinations(Y,2):
                if aligned(a,b): continue
                S2lo+=L                     # X_l >= q^3-q too
            for tr in combinations(Y,3):
                if any(aligned(a,b) for a,b in combinations(tr,2)): continue
                if online(tr): continue      # handled below
                S3hi+=T3
            # rich-line triples: +X_l each; their pairs were counted at -L above, i.e. -X_l replaced by -L.
            # net coefficient of X_l is -(C(m,2)-C(m,3)) <= 0, so bound pairs by L and add C(m,3)*X_l back
            # as C(m,3)*X_l with X_l-coefficient: we need -C(m,2)X + C(m,3)X <= -(C(m,2)-C(m,3))L.
            # S2lo already has -C(m,2)L; add +C(m,3)L (valid since C(m,2)-C(m,3) >= 0 for m<=4).
            for l in rich:
                m=len(l); c2=m*(m-1)//2; c3=m*(m-1)*(m-2)//6
                assert c2-c3>=0
                S3hi+=c3*L
            U=S1-S2lo+S3hi
        far=q**5-U-m2*q*q
        forced=sum(len(c)+len(c)*(len(c)-1)//2 for c in cls if len(c)>=2)+sum(len(l)*(len(l)-1)//2 for l in rich)
        key=(tuple(sorted(len(c) for c in cls)),tuple(sorted(len(l) for l in rich)))
        if key not in types: types[key]=(far,forced,far,forced)
        f0,p0,f1,p1=types[key]
        types[key]=(min(f0,far),min(p0,forced),max(f1,far),max(p1,forced))
print("q=%d m2=%d: %d labelled configurations, %d types"%(q,m2,nlab,len(types)))
bad=[]
for k,(fmin,pmin,fmax,pmax) in sorted(types.items(),key=lambda kv:kv[1][0]):
    print("  classes %-16s rich %-8s far >= %6d (max over labellings %6d)  forced perp pairs %d..%d"%(k[0],k[1],fmin,fmax,pmin,pmax))
    if fmin<=0: bad.append(pmin)
print("types with no far vertex forced: %d; min forced perpendicular pairs among them: %d"%(len(bad),min(bad)))
