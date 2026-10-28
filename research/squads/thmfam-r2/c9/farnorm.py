"""For the far layer of the BFS from (e,A): min integer norm of a quaternion lift of each far group element.
usage: farnorm.py mode p q NMAX"""
import sys, math, collections
mode,p,q,NMAX=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
W='/home/user/degree-diameter/research/squads/thmfam-r2/c9/work'
I=((0,q-1),(1,0)); x=y=None
for xx in range(q):
    yy=next((v for v in range(q) if (v*v+xx*xx+3)%q==0),None)
    if yy is not None: x,y=xx,yy; break
J=((x,y),(y,(-x)%q)); IJ=tuple(tuple(sum(A*B for A,B in zip(ra,cb))%q for cb in zip(*J)) for ra in I)
def lin(a):
    f=lambda r,c: (a[0]*(r==c)+a[1]*I[r][c]+a[2]*J[r][c]+a[3]*IJ[r][c])%q
    return [f(0,0),f(0,1),f(1,0),f(1,1)]
def pn(v):
    f=next(t for t in v if t); s=pow(f,q-2,q); return tuple(t*s%q for t in v)
best={}
R=int(math.isqrt(NMAX))+1
for a0 in range(-R,R+1):
  for a1 in range(-R,R+1):
    for a2 in range(-R,R+1):
      for a3 in range(-R,R+1):
        n=a0*a0+a1*a1+3*a2*a2+3*a3*a3
        if n==0 or n>NMAX: continue
        k=pn(lin((a0,a1,a2,a3)))
        if k not in best or best[k]>n: best[k]=n
far=[l.split() for l in open(f'{W}/last_{mode}_{p}_{q}.txt')]
cnt=collections.Counter(); sides=collections.Counter()
for l in far:
    side=int(l[0]); g=tuple(int(t) for t in l[1:])
    v=[g[0],g[1],g[2],g[3]]
    key=pn([v[0],v[1],v[2],v[3]])
    cnt[best.get(key,'>%d'%NMAX)]+=1; sides[side]+=1
print(f"mode={mode} p={p} q={q} far_layer_size={len(far)} sides={dict(sides)} NMAX={NMAX} lift-norm histogram:",sorted(cnt.items(),key=lambda t:str(t[0])))
