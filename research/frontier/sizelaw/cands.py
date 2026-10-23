import math
from data import *
from sympy import factorint
def pp(q): f=factorint(q); return len(f)==1
qs=[q for q in range(4,400) if pp(q)]
def sl(q): return q*(q*q-1)
def psl(q): return sl(q)//(2 if q%2 else 1)
fam=[]
for q in qs:
    for n in range(1,41):
        fam.append(('sl %d x Z_%d'%(q,n),sl(q)*n)); 
        if q%2: fam.append(('psl %d x Z_%d'%(q,n),psl(q)*n))
for q1 in [5,7,8,9,11,13]:
    for q2 in qs:
        if q2<=q1: continue
        for n in range(1,9): fam.append(('sl %d x sl %d x Z_%d'%(q1,q2,n),sl(q1)*sl(q2)*n))
import json
P={(o['d'],o['D']):o for o in json.load(open('pred.json'))}
for (d,D) in [(10,10),(12,9),(13,9),(15,8),(14,9)]:
    t=P[(d,D)]['table']; need=t//2+1; nh=Nh(d,D); npred=P[(d,D)]['pred']//2
    print('(%d,%d) table %d need N>=%d, N_h %d, pred N %d'%(d,D,t,need,nh,npred))
    sel=sorted([f for f in fam if need<=f[1]<=npred*1.02],key=lambda f:f[1])
    # pick: smallest few above need, and a few nearest 0.80 N_h and nearest pred
    pick=sel[:4]+sorted(sel,key=lambda f:abs(f[1]-0.80*nh))[:3]+sorted(sel,key=lambda f:abs(f[1]-npred))[:3]
    seen=set()
    for s,N in pick:
        if s in seen: continue
        seen.add(s); print('   %-24s N=%d  vertices %d  N/N_h %.3f  gain vs table %+.1f%%'%(s,N,2*N,N/nh,100*(2*N/t-1)))
