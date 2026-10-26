import itertools
vecs=[]
for v in itertools.product(range(3),repeat=3):
    if v==(0,0,0): continue
    first=[x for x in v if x][0]
    if first==1: vecs.append(v)
assert len(vecs)==13
edges=[]
for i,p in enumerate(vecs):
    for j,l in enumerate(vecs):
        if sum(a*b for a,b in zip(p,l))%3==0:
            edges.append((i,13+j))
assert len(edges)==52
with open('pg23.txt','w') as f:
    f.write(f"26 {len(edges)}\n")
    for u,v in edges: f.write(f"{u} {v}\n")
print(len(edges))
