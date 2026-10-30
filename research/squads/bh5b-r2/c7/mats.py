import itertools, sys
# enumerate 3x3 nonneg integer matrices with row/col sums 5, connected bipartite, up to row/col perms and transpose
rows=[r for r in itertools.product(range(6),repeat=3) if sum(r)==5]
mats=[]
for a in rows:
  for b in rows:
    c=tuple(5-a[j]-b[j] for j in range(3))
    if min(c)<0 or sum(c)!=5: continue
    M=(a,b,c)
    mats.append(M)
def canon(M):
    best=None
    for p in itertools.permutations(range(3)):
        for q in itertools.permutations(range(3)):
            for T in (False,True):
                N=[[M[p[i]][q[j]] for j in range(3)] for i in range(3)]
                if T: N=[[N[j][i] for j in range(3)] for i in range(3)]
                t=tuple(tuple(r) for r in N)
                if best is None or t<best: best=t
    return best
def connected(M):
    # bipartite graph on 6 vertices
    adj={v:set() for v in range(6)}
    for i in range(3):
        for j in range(3):
            if M[i][j]>0: adj[i].add(3+j); adj[3+j].add(i)
    seen={0}; st=[0]
    while st:
        v=st.pop()
        for w in adj[v]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen)==6
reps={}
for M in mats:
    if not connected(M): continue
    c=canon(M)
    reps.setdefault(c,0)
print(len(reps))
for r in sorted(reps): print(r)
