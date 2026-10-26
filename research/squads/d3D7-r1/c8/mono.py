# exhaustive search over families f_i = c * mono_i (one monomial per equation), mono from a small list of
# bilinear / linear monomials in earlier coordinates. ms = moduli. usage: mono.py ms [out.edges]
import sys, itertools, time, math; sys.path.insert(0,'/home/user/degree-diameter/research/squads/d3D7-r1/c8')
from alg import build, score, write_edges
ms=[int(x) for x in sys.argv[1].split(',')]; out=sys.argv[2] if len(sys.argv)>2 and sys.argv[2]!='-' else None
k=len(ms)
def monos(i):
    P=lambda j:('p',j); L=lambda j:('l',j)
    cand=[(),(P(i-1),),(L(i-1),),(P(1),),(L(1),),
          tuple(sorted((P(1),L(1)))), tuple(sorted((P(i-1),L(1)))), tuple(sorted((L(i-1),P(1)))),
          tuple(sorted((P(i-1),L(i-1)))), tuple(sorted((P(i-1),P(1)))), tuple(sorted((L(i-1),L(1)))),
          tuple(sorted((P(1),P(1)))), tuple(sorted((L(1),L(1))))]
    return list(dict.fromkeys(cand))
opts=[]
for i in range(2,k+1):
    o=[]
    for mo in monos(i):
        for c in range(1,ms[i-1]): o.append({mo:c})
    opts.append(o)
best=None; t0=time.time(); cnt=0
for combo in itertools.product(*opts):
    r=build(ms,list(combo))
    if r is None: continue
    n,adj=r; cnt+=1
    bad,diam=score(n,adj)
    if best is None or (bad,diam)<(best[0],best[1]):
        best=(bad,diam,combo); print('bad',bad,'diam',diam,[list(d.items()) for d in combo],flush=True)
        if bad==0 and out: write_edges(n,adj,out); print('WROTE',out,flush=True)
print('done n=',2*math.prod(ms),'regular combos',cnt,'best',best[:2] if best else None,'time',round(time.time()-t0,1))
