import bisect
exec(open('enum.py').read().split('F=out')[0])
F=sorted(out,key=lambda t:t[3])
Ns=[t[3] for t in F]
res=[]
for a in F:
    lo=-(-1056058//a[3]); hi=1065000//a[3]
    i=bisect.bisect_left(Ns,lo); j=bisect.bisect_right(Ns,hi)
    for b in F[i:j]:
        if (a[1],a[0])>(b[1],b[0]): continue
        if max(a[1],b[1])<17: continue
        res.append((a[3]*b[3],a,b))
res.sort()
for N,a,b in res: print(N, "meta %d %d %d"%(a[0],a[1],a[2]), "meta %d %d %d"%(b[0],b[1],b[2]))
print(len(res), len(F))
