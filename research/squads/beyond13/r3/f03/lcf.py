from walks import walks, distinct_counts
def lcf(n, shifts, reps):
    edges=set()
    for i in range(n): edges.add(tuple(sorted((i,(i+1)%n))))
    for i,s in enumerate(shifts*reps):
        pass
    L=len(shifts)*reps
    for i in range(n):
        j=(i+ (shifts[i%len(shifts)]))%n
        edges.add(tuple(sorted((i,j))))
    return n, sorted(edges)
V,edges=lcf(30,[-13,-9,7,-7,9,13],5)
deg=[0]*V
for a,b in edges: deg[a]+=1; deg[b]+=1
print("V",V,"E",len(edges),"degs",set(deg))
import collections
out=walks(V,edges,0,13)
for L in (10,12,13):
    d,per=distinct_counts(V,out,L)
    tot=sum(len(x[0]) for x in out[:L+1])
    print(f"tutte8 L<={L} walks={tot} distinct={d} ratio={d/tot:.4f} per_end_min={per.min()} max={per.max()}")
