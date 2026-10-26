# usage: prep.py VOLT MODE SEED OUT   (MODE: orig | rand)  -> input file for rewire
import sys, random
sys.path.insert(0,'/home/user/degree-diameter/research/squads/b48/r2/b09')
from classes import G, E, N
volt=int(sys.argv[1]); mode=sys.argv[2]; seed=int(sys.argv[3]); out=sys.argv[4]
cls={}
for a,b in E:
    if a>=N: a,b=b,a
    g=G.mul(G.inv(a), b-N)
    cls.setdefault(g,[]).append((a,b))
fixed=[e for g,L in cls.items() if g!=volt for e in L]
var=sorted(cls[volt])
if mode=='rand':
    rnd=random.Random(seed)
    forb=set(fixed)
    while True:
        perm=list(range(N,2*N)); rnd.shuffle(perm)
        pairs=[(a,perm[a]) for a in range(N)]
        if not any(p in forb for p in pairs): break
    var=pairs
else:
    var=[(a,b) for a,b in var]
    var.sort()
with open(out,'w') as f:
    f.write(f"{2*N}\n{len(fixed)}\n")
    for a,b in fixed: f.write(f"{a} {b}\n")
    f.write(f"{len(var)}\n")
    for a,b in var: f.write(f"{a} {b}\n")
print('fixed',len(fixed),'var',len(var))
