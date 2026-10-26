import itertools, sys
# 3x3 nonnegative integer matrices, row/col sums 3, connected, up to row/col permutations
def mats():
    rows=[r for r in itertools.product(range(4),repeat=3) if sum(r)==3]
    for a in rows:
        for b in rows:
            for c in rows:
                if a[0]+b[0]+c[0]==3 and a[1]+b[1]+c[1]==3 and a[2]+b[2]+c[2]==3:
                    yield (a,b,c)
def canon(M):
    best=None
    for p in itertools.permutations(range(3)):
        for q in itertools.permutations(range(3)):
            N=tuple(tuple(M[p[i]][q[j]] for j in range(3)) for i in range(3))
            if best is None or N<best: best=N
    return best
def connected(M):
    seen={0}; st=[0]
    # vertices: A0..A2 = 0..2, B0..B2 = 3..5
    while st:
        v=st.pop()
        if v<3:
            nb=[3+j for j in range(3) if M[v][j]>0]
        else:
            nb=[i for i in range(3) if M[i][v-3]>0]
        for w in nb:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen)==6
classes={}
for M in mats():
    if not connected(M): continue
    c=canon(M)
    classes.setdefault(c,0)
out=[]
for c in sorted(classes):
    edges=[]
    for i in range(3):
        for j in range(3):
            edges += [(i,3+j)]*c[i][j]
    out.append((c,edges))
for k,(c,edges) in enumerate(out):
    fn=f"base33_{k}.txt"
    with open(fn,'w') as f:
        f.write(f"6 {len(edges)}\n")
        for u,v in edges: f.write(f"{u} {v}\n")
    print(fn, c, edges)
