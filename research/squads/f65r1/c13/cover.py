import itertools, random
q=7
def norm(v):
    v=[x%q for x in v]
    for x in v:
        if x:
            inv=pow(x,q-2,q)
            return tuple((y*inv)%q for y in v)
    return None
PG=sorted({norm(v) for v in itertools.product(range(q),repeat=3) if any(v)})
assert len(PG)==57
def cross(a,b):
    return norm((a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]))
def dot(a,b): return sum(x*y for x,y in zip(a,b))%q
def uncovered(S):
    lines=set()
    for a,b in itertools.combinations(S,2):
        lines.add(cross(a,b))
    cov=set(S)
    for d in PG:
        if d in cov: continue
        for n in lines:
            if dot(n,d)==0:
                cov.add(d); break
    return 57-len(cov), len(lines)
random.seed(1)
best=None; hist={}
for t in range(20000):
    S=random.sample(PG,7)
    u,nl=uncovered(S)
    hist[u]=hist.get(u,0)+1
    if u==0:
        print("FOUND", S, nl); break
print(sorted(hist.items())[:10])
