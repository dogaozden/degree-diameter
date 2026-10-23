import math, numpy as np, json, os
from data import *
rows=sols(); best={}
for r in rows:
    k=(r['d'],r['D'])
    if k not in best or r['N']>best[k]['N']: best[k]=r
B=list(best.values())
x=np.array([math.log(r['N']) for r in B]); y=np.array([math.log(mu(r['d'],r['D'],r['N'])) for r in B])
A=np.vstack([np.ones_like(x),x]).T; coef,res,_,_=np.linalg.lstsq(A,y,rcond=None); a,b=coef
e=y-A@coef; sd=e.std(ddof=2)
cov=sd**2*np.linalg.inv(A.T@A)
print('ln mu* = %.3f + %.3f ln N   (se a %.3f, se b %.3f), resid sd %.3f'%(a,b,math.sqrt(cov[0,0]),math.sqrt(cov[1,1]),sd))
for r,ei in zip(B,e): r['res']=ei
for par in (0,1):
    v=[r['res'] for r in B if r['D']%2==par]; print('parity','even' if par==0 else 'odd','mean resid %.3f (n=%d, se %.3f)'%(np.mean(v),len(v),np.std(v,ddof=1)/math.sqrt(len(v))))
# leave-one-out check of predictive accuracy in N
loo=[]
for i,r in enumerate(B):
    m=np.ones(len(B),bool); m[i]=False
    c2=np.linalg.lstsq(A[m],y[m],rcond=None)[0]
    Np=solve(r['d'],r['D'],c2) if False else None
def Npred(d,D,a,b,shift=0.0):
    w=W(d,D); lo,hi=10.0,float(w)
    for _ in range(200):
        m=(lo+hi)/2
        if math.log(m)-w/m < a+b*math.log(m)+shift: lo=m
        else: hi=m
    return lo
for i,r in enumerate(B):
    m=np.ones(len(B),bool); m[i]=False
    c2=np.linalg.lstsq(A[m],y[m],rcond=None)[0]
    loo.append(math.log(r['N']/Npred(r['d'],r['D'],*c2)))
loo=np.array(loo); print('leave-one-out log error in N: rms %.3f, max %.3f'%(np.sqrt((loo**2).mean()),abs(loo).max()))
for r,l in zip(B,loo): print('  (%d,%d) LOO %+.3f'%(r['d'],r['D'],l))
import sys; sys.path.insert(0,os.path.expanduser('~/AI_Projects/degree-diameter/research/frontier'))
from heuristic import TABLE
rec={(x['degree'],x['diameter']):x['ours'] for x in json.load(open(os.path.expanduser('~/AI_Projects/research-lab/records.json')))}
out=[]
for D in (5,7,8,9,10):
    for d in range(3,17):
        t=TABLE[d][D-3]
        if D==5 and d==3: continue
        Np=Npred(d,D,a,b); lo=Npred(d,D,a,b,+2*sd); hi=Npred(d,D,a,b,-2*sd)
        nh=Nh(d,D); ours=rec.get((d,D))
        out.append(dict(d=d,D=D,table=t,ours=ours,pred=2*int(Np),lo=2*int(lo),hi=2*int(hi),Nh2=2*int(nh),
            need=None if t is None else (t/2)/Np, ceil=None if t is None else (t/2)/nh))
json.dump(out,open('pred.json','w'))
print('cell table ours pred[2sd band] 2N_h  table/pred  table/ceiling')
for o in out:
    print('(%d,%d) %s %s %s [%s-%s] %s %s %s'%(o['d'],o['D'],o['table'],o['ours'],o['pred'],o['lo'],o['hi'],o['Nh2'],
        '-' if o['need'] is None else '%.3f'%o['need'],'-' if o['ceil'] is None else '%.3f'%o['ceil']))
