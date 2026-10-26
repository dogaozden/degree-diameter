import collections
f=open('/home/user/degree-diameter/research/fresh65/seeds/d6D5_n630_A3_2_chambers.edges').read().split()
n=int(f[0]); E=[(int(f[i]),int(f[i+1])) for i in range(1,len(f),2)]
adj=[[] for _ in range(n)]
for u,v in E: adj[u].append(v); adj[v].append(u)
col=[-1]*n; col[0]=0; q=[0]
for u in q:
    for v in adj[u]:
        if col[v]<0: col[v]=1-col[u]; q.append(v)
# number of walks of length exactly 2 and 4 that are non-backtracking, between same-side pairs
mult=collections.Counter()
single=0; tot=0
for s in range(n):
    # non-backtracking paths of length 4 from s
    c=collections.Counter()
    for a in adj[s]:
        for b in adj[a]:
            if b==s: continue
            c[b]+=1
            for x in adj[b]:
                if x==a: continue
                for y in adj[x]:
                    if y==b: continue
                    c[y]+=1
    # c counts length-2 and length-4 (non-backtracking walks, possibly non-simple)
    for t in range(n):
        if t!=s and col[t]==col[s]:
            tot+=1
            if c[t]==1: single+=1
print("same-side ordered pairs",tot,"pairs with exactly 1 nb-walk of length<=4 (incl. length2 walks)",single)
