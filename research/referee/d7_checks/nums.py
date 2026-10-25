def N(q): return (q**6-1)//(q-1)
def ispp(n):
    if n<2: return False
    p=next(d for d in range(2,n+1) if n%d==0)
    while n%p==0: n//=p
    return n==1
def kappa(d):
    return max((s*s+s+1)*(1+(d-s-1)*d) for s in range(2,d) if ispp(s))
print("kappa",{d:kappa(d) for d in (3,4,5,6,7,8,9,10,11,14)})
cells=[(7,5,1,23436,23598),(9,7,1,117648,118238),(10,8,1,224694,225152),(11,9,1,398580,413180),(12,9,2,664300,693500),
       (13,11,1,1062936,1064472),(14,11,2,1771560,1789588),(15,11,3,2480184,2501491),(16,13,2,4022340,4052108)]
for D_,q,r,tab,ours in cells:
    base=(2*r+1)*2*N(q)
    best=max(((2*rr+1)*2*N(qq),qq,rr) for qq in range(2,D_) if ispp(qq) for rr in [D_-qq-1] if rr>=1)
    print((D_,7),"q",q,"r",r,"base",base,"table",tab,base==tab,"max form",best,"gain",ours-base)
print("hub sums:",23436+162,117648+590,224694+458,398580+14600,664300+29200,1062936+1536,1771560+18028,2480184+10826+10481,4022340+29768)
# Cor 9.3 crossover
out=[]
for q in range(5,400):
    if not ispp(q): continue
    a=(q+2)*(q*q+1); k=kappa(q-2)
    out.append((q,'kappa' if k<a else 'slots'))
print("Cor 9.3 min attained by:",out[:12])
print("any slots-limited q<=13 or kappa-limited q>=16:",[x for x in out if (x[0]<=13 and x[1]!='kappa') or (x[0]>=16 and x[1]!='slots')])
# Cor 9.1: kappa(q-1) >= q^2+1 for q>=5
print("Cor 9.1 q>=5 kappa(q-1)>=q^2+1 fails at:",[q for q in range(5,400) if ispp(q) and kappa(q-1)<q*q+1], "q=4:",kappa(3),17)
# Cor 9.2: kappa(q-r) < q^4 < r(q+1)(q^3+1)
print("Cor 9.2 check:",all(kappa(q-r)<q**4 for q in (9,27,81) for r in range(1,q-2)))
# Remark 9.4
print("Rem 9.4:",12*1332,12*756,1771560+2*(9072+768))
# HDHDH (16,7) and Cor 9.3 slot formulas
fP,fL,m=14762,14823,122; print("(16,7) KB",min(fP+m,fL+m,2*fL),"KA",min(fL+m,2*fP,fP+m))
fP,fL,m=8645,8246,768; print("(14,7) alpha",(fP+m,fL+m,fP+m,2*fL,m+fP),"beta",(m+fL,2*fP,fL+m,fP+m,fL+m))
# seven-level HHDHDHD friendly count
t="HHDHDHD"; fr=[(j,k) for j in range(7) for k in (1,2,3) if t[j]!=t[(j+k)%7]]
print("HHDHDHD friendly",len(fr))
for j in range(7):
    o=sum(1 for (a,k) in fr if a==j); i=sum(1 for (a,k) in fr if (a+k)%7==j); print(" level",j,t[j],"out",o,"in",i)
# 4/27 asymptotics
print([ (d,kappa(d), round(4*d**4/27)) for d in (10,20,40)])
