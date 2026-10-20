import collections
from hexbin import load
q,N,lines,crd=load(5); lines=lines.tolist()
S=[int(x) for x in open('runs/S_q5_s1.txt').read().split()]; v=S[0]
W=[int(x) for x in open('runs/W_q5_sat.txt').read().split()]
spt={p:s for s in S for p in lines[s]}
thr=[[] for _ in range(N)]
for k,L in enumerate(lines):
    for p in L: thr[p].append(k)
def adj(x):  # vertices: points 0..N-1, lines N+k
    return [N+k for k in thr[x]] if x<N else lines[x-N]
def dist_from(x,maxd=6):
    d={x:0}; fr=[x]
    for r in range(1,maxd+1):
        nf=[]
        for y in fr:
            for z in adj(y):
                if z not in d: d[z]=r; nf.append(z)
        fr=nf
    return d
byS=collections.defaultdict(list)
for w in W:
    s=[spt[p] for p in lines[w] if p in spt][0]; byS[s].append(w)
res=collections.Counter()
for s,ws in list(byS.items())[:20]:
    ds=[dist_from(N+w) for w in ws]
    common=[t for t in range(N,2*N) if all(d.get(t)==4 for d in ds)]
    common_pts=[x for x in range(N) if all(d.get(x)==3 for d in ds)]
    ds_s=dist_from(N+s)
    res[(len(common), tuple(sorted(ds_s.get(t) for t in common)), len(common_pts))]+=1
print(res)
B=set(int(x) for x in open('runs/B_q5_line0.txt').read().split())
Sset=set(S)
dv=dist_from(N+v)
res2=collections.Counter()
for s,ws in byS.items():
    ds=[dist_from(N+w) for w in ws]
    common=[t-N for t in range(N,2*N) if all(d.get(t)==4 for d in ds)]
    res2[tuple(sorted(('S' if t in Sset else '-')+('B' if t in B else '-')+('v' if t==v else '')+str(dv[N+t]) for t in common))]+=1
print(res2)
res3=collections.Counter(); allT=collections.Counter()
for s,ws in byS.items():
    ds=[dist_from(N+w) for w in ws]
    common=[t-N for t in range(N,2*N) if all(d.get(t)==4 for d in ds)]
    sig=[[spt[p] for p in lines[t] if p in spt][0] for t in common]
    for t in common: allT[t]+=1
    res3[(tuple(sorted('B' if x in B else ('s' if x==s else 'A') for x in sig)), len(set(sig)))]+=1
print(res3); print('distinct t', len(allT), collections.Counter(allT.values()))
