# sample random connected cubic bipartite 5+5 multigraphs (config model), dedupe up to row/col perms
import random, itertools, sys, os
n=5; rng=random.Random(int(sys.argv[2])); out=sys.argv[1]; os.makedirs(out,exist_ok=True)
def conn(M):
    seenA={0}; seenB=set(); st=[('A',0)]
    while st:
        t,x=st.pop()
        if t=='A':
            for j in range(n):
                if M[x][j]>0 and j not in seenB: seenB.add(j); st.append(('B',j))
        else:
            for i in range(n):
                if M[i][x]>0 and i not in seenA: seenA.add(i); st.append(('A',i))
    return len(seenA)==n and len(seenB)==n
def canon(M):
    best=None
    for p in itertools.permutations(range(n)):
        R=[M[i] for i in p]
        key=tuple(sorted(tuple(R[i][j] for i in range(n)) for j in range(n)))
        if best is None or key<best: best=key
    return best
seen={}
for _ in range(int(sys.argv[3])):
    pts=[i for i in range(n) for _ in range(3)]; cols=[j for j in range(n) for _ in range(3)]
    rng.shuffle(cols)
    M=[[0]*n for _ in range(n)]
    for a,b in zip(pts,cols): M[a][b]+=1
    if not conn(M): continue
    c=canon(M)
    if c not in seen: seen[c]=M
print('classes',len(seen),file=sys.stderr)
for k,M in enumerate(seen.values()):
    with open(os.path.join(out,f"c{k}.txt"),'w') as f:
        f.write("10\n")
        for i in range(n):
            for j in range(n):
                for _ in range(M[i][j]): f.write(f"{i} {n+j}\n")
    print(k, M, file=sys.stderr)
