import sys, collections
H=16896
orbs=[list(map(int,l.split())) for l in open(sys.argv[1]) if l.strip()]
def key(t): return ((t>>8)//22)*256 + (t&255)
allk=set(); bad=0; jd=collections.Counter(); per=[]
for N in orbs:
    ks=[key(t) for t in N]
    if len(set(ks))!=len(ks): bad+=1
    for k in ks:
        if k in allk: bad+=1
        allk.add(k)
    per.append(sorted(set(k//256 for k in ks)))
    for t in N: jd[(t>>8)//22]+=1
print("orbits",len(orbs),"sizes",collections.Counter(len(N) for N in orbs),"keys used",len(allk),"conflicts",bad)
print("j-distribution of keys",dict(jd))
print("j-sets per orbit",collections.Counter(tuple(p) for p in per))
