# random search over B(f_2..f_k): each f_i = random sum of <=T monomials (degree <=2 in earlier coords)
import sys, random, time; sys.path.insert(0,'/home/user/degree-diameter/research/squads/d3D7-r1/c8')
from alg import *
ms=[int(x) for x in sys.argv[1].split(',')]; trials=int(sys.argv[2]); seed=int(sys.argv[3]); T=int(sys.argv[4]) if len(sys.argv)>4 else 3
out=sys.argv[5] if len(sys.argv)>5 else None
rnd=random.Random(seed); k=len(ms)
best=None; t0=time.time(); hist={}
for tr in range(trials):
    fs=[]
    for i in range(2,k+1):
        vars_=[('p',j) for j in range(1,i)]+[('l',j) for j in range(1,i)]
        mons=[()]+[(v,) for v in vars_]+[tuple(sorted(c)) for c in __import__('itertools').combinations_with_replacement(vars_,2)]
        d={}
        for _ in range(rnd.randint(1,T)):
            mono=rnd.choice(mons); c=rnd.randrange(1,ms[i-1])
            d[mono]=(d.get(mono,0)+c)%ms[i-1]
        fs.append({a:b for a,b in d.items() if b})
    r=build(ms,fs)
    if r is None: continue
    n,adj=r; bad,diam=score(n,adj)
    hist[bad]=hist.get(bad,0)+1
    if best is None or bad<best[0]:
        best=(bad,diam,fs); print('trial',tr,'bad',bad,'diam',diam,fs,flush=True)
        if bad==0 and out: write_edges(n,adj,out); print('WROTE',out,flush=True)
print('done',trials,'time',round(time.time()-t0,1),'best',best[:2] if best else None)
print('hist(smallest 8)',sorted(hist.items())[:8])
