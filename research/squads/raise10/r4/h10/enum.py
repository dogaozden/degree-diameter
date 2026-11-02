# enumerate connected cubic bipartite multigraphs on 5+5 up to row/col permutation (5x5 nonneg int matrices, line sums 3)
import itertools, sys
n=5
rows=[r for r in itertools.product(range(4),repeat=n) if sum(r)==3]
seen=set(); reps=[]
def conn(M):
    # bipartite connectivity
    adjA={i:[j for j in range(n) if M[i][j]>0] for i in range(n)}
    adjB={j:[i for i in range(n) if M[i][j]>0] for j in range(n)}
    seenA={0}; seenB=set(); st=[('A',0)]
    while st:
        t,x=st.pop()
        if t=='A':
            for j in adjA[x]:
                if j not in seenB: seenB.add(j); st.append(('B',j))
        else:
            for i in adjB[x]:
                if i not in seenA: seenA.add(i); st.append(('A',i))
    return len(seenA)==n and len(seenB)==n
def canon(M):
    best=None
    for p in itertools.permutations(range(n)):
        R=[M[i] for i in p]
        cols=sorted(tuple(R[i][j] for i in range(n)) for j in range(n))
        key=tuple(cols)
        if best is None or key<best: best=key
    return best
allM=[]
def rec(i,colrem,acc):
    if i==n:
        if all(c==0 for c in colrem): allM.append(tuple(acc))
        return
    for r in rows:
        if all(r[j]<=colrem[j] for j in range(n)):
            rec(i+1,[colrem[j]-r[j] for j in range(n)],acc+[r])
rec(0,[3]*n,[])
print('matrices',len(allM),file=sys.stderr)
for M in allM:
    if not conn(M): continue
    c=canon(M)
    if c in seen: continue
    seen.add(c); reps.append(M)
print(len(reps), file=sys.stderr)
import os
out=sys.argv[1]; os.makedirs(out,exist_ok=True)
for k,M in enumerate(reps):
    E=[]
    for i in range(n):
        for j in range(n):
            for _ in range(M[i][j]): E.append((i, n+j))
    with open(os.path.join(out,f"c{k}.txt"),'w') as f:
        f.write(f"{2*n}\n")
        for a,b in E: f.write(f"{a} {b}\n")
    print(k, sum(1 for i in range(n) for j in range(n) if M[i][j]>1), M, file=sys.stderr)
