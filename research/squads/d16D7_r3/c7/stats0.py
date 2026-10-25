import random, collections, statistics, sys
R2="/home/user/degree-diameter/research/squads/d16D7_r2/"
R3="/home/user/degree-diameter/research/squads/d16D7_r3/"
g="pts"
with open(R2+"og_%s.txt"%g) as f:
    M,E=map(int,f.readline().split())
    adj=[None]*M
    for line in f:
        a=list(map(int,line.split()))
        adj[a[0]]=a[3:3+a[2]]
print("deg min/max/avg", min(map(len,adj)), max(map(len,adj)), sum(map(len,adj))/M, flush=True)
S=set(int(x) for x in open(R3+"seed_%s.txt"%g) if x.strip())
conf=[0]*M
for v in S:
    for u in adj[v]: conf[u]+=1
print("indep", all(conf[v]==0 for v in S), "free outside S", sum(1 for v in range(M) if v not in S and conf[v]==0), flush=True)
print("conf histogram over non-solution:", sorted(collections.Counter(conf[v] for v in range(M) if v not in S).items())[:14], flush=True)
blocks=[list(map(int,l.split())) for l in open(R3+"quot/q9_%s.map"%g)]
Sblocks=[b for b in blocks if any(v in S for v in b)]
print("solution blocks", len(Sblocks), flush=True)
random.seed(1)
for k in [3,5,8,10]:
    ms=[]; ints=[]; rems=[]
    for trial in range(8):
        ch=random.sample(Sblocks,k)
        rem=set(v for b in ch for v in b if v in S)
        S2=S-rem
        c2=[0]*M
        for v in S2:
            for u in adj[v]: c2[u]+=1
        C=[v for v in range(M) if v not in S2 and c2[v]==0]
        Cs=set(C)
        ie=sum(1 for v in C for u in adj[v] if u in Cs)//2
        ms.append(len(C)); ints.append(ie); rems.append(len(rem))
    print("k",k,"removed",statistics.mean(rems),"C mean",statistics.mean(ms),"min",min(ms),"max",max(ms),"internal edges mean",statistics.mean(ints), flush=True)
