# Build PG(6,3) via GF(3^7) (Singer cycle): 1093 points, 99463 lines (4 points each).
# Writes orbits.txt: K, then K blocks of 1093 lines "p1 p2 p3 p4" (one Singer orbit of lines each).
import itertools, numpy as np
Q=2187; N=2186; PN=1093
def mulx(d,a):
    top=d[6]; nd=[0]+d[:6]
    return [(nd[i]+top*a[i])%3 for i in range(7)]
found=None
for a in itertools.product(range(3),repeat=7):
    if a[0]==0: continue
    d=[1,0,0,0,0,0,0]; ok=False
    for k in range(1,N+1):
        d=mulx(d,a)
        if d==[1,0,0,0,0,0,0]:
            ok=(k==N); break
    if ok: found=a; break
print("primitive poly tail a =",found)
pw=[]; d=[1,0,0,0,0,0,0]
for i in range(N):
    pw.append(d); d=mulx(d,found)
pow3=3**np.arange(7)
enc=lambda d: int(sum(d[i]*3**i for i in range(7)))
LOG=np.full(Q,-1,dtype=np.int64)
for i,d in enumerate(pw): LOG[enc(d)]=i
assert all((pw[i+PN][k]+pw[i][k])%3==0 for i in range(PN) for k in range(7))  # alpha^{1093} = -1
P=np.array(pw[:PN])
I,J=np.triu_indices(PN,1)
U=P[I]; V=P[J]
S=(U+V)%3; T=(U-V)%3
ps=LOG[S@pow3]%PN; pt=LOG[T@pow3]%PN
L=np.sort(np.stack([I,J,ps,pt],axis=1),axis=1)
L=np.unique(L,axis=0)
print("lines:",len(L))
assert len(L)==99463
seen=set(map(tuple,L.tolist()))
orbits=[]
done=set()
for line in map(tuple,L.tolist()):
    if line in done: continue
    orb=[]
    for s in range(PN):
        t=tuple(sorted((x+s)%PN for x in line))
        orb.append(t); done.add(t)
    assert len(set(orb))==PN
    orbits.append(orb)
print("orbits:",len(orbits))
with open("orbits.txt","w") as f:
    f.write(f"{len(orbits)}\n")
    for orb in orbits:
        for t in orb: f.write(" ".join(map(str,t))+"\n")
