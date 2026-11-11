# H-marginal screen (same Poisson model as hscan/hmarg) for H = F_81 x| mu_5 x Z_3 (order 1215).
# Elements (v, j, z): v in F_81 (int 0..80), j in Z_5, z in Z_3. (v,j,z)(w,k,y) = (v + zeta^j w, j+k, z+y).
# beta(v,j,z) = (zeta v, j, z): an order-5 automorphism. Orbit of s = (v, j0, z0): (zeta^i v, j0, z0).
import math, sys
from collections import defaultdict
P=3
def polymul(a,b,mod):  # a,b lists of 4 coeffs (low->high); mod: monic x^4 + c3 x^3 + ... as list c[0..3]
    r=[0]*7
    for i in range(4):
        for k in range(4):
            r[i+k]=(r[i+k]+a[i]*b[k])%P
    for d in range(6,3,-1):
        co=r[d]
        if co:
            r[d]=0
            for t in range(4):
                r[d-4+t]=(r[d-4+t]-co*mod[t])%P
    return r[:4]
def enc(c): return c[0]+3*c[1]+9*c[2]+27*c[3]
def dec(n): return [n%3,(n//3)%3,(n//9)%3,(n//27)%3]
found=None
import itertools
for mod in itertools.product(range(3),repeat=4):
    if mod[0]==0: continue
    # order of x
    x=[0,1,0,0]; cur=[1,0,0,0]; order=None
    for k in range(1,82):
        cur=polymul(cur,x,mod)
        if cur==[1,0,0,0]:
            order=k; break
    if order==80:
        found=mod; break
mod=found
MUL=[[enc(polymul(dec(a),dec(b),mod)) for b in range(81)] for a in range(81)]
ADD=[[enc([(x+y)%3 for x,y in zip(dec(a),dec(b))]) for b in range(81)] for a in range(81)]
NEG=[enc([(-x)%3 for x in dec(a)]) for a in range(81)]
# zeta = x^16 (order 5)
xpow=[1,0,0,0]
for _ in range(16): xpow=polymul(xpow,[0,1,0,0],mod)
zeta=enc(xpow)
zp=[1]
for _ in range(4): zp.append(MUL[zp[-1]][zeta])
assert zp[4]!=1 and MUL[zp[4]][zeta]==1
def hmul(x,y):
    v,j,z=x; w,k,t=y
    return (ADD[v][MUL[zp[j]][w]], (j+k)%5, (z+t)%3)
def hinv(x):
    v,j,z=x
    # (v,j,z)^-1 = (-zeta^{-j} v, -j, -z)
    zi=zp[(5-j)%5]
    return (NEG[MUL[zi][v]], (5-j)%5, (3-z)%3)
def walk_vals(S,L=11):
    Sinv=[hinv(s) for s in S]
    dist={((0,0,0),-1):1}
    for t in range(1,L+1):
        nd=defaultdict(int)
        letters = S if t%2==1 else Sinv
        for (h,last),c in dist.items():
            for i,s in enumerate(letters):
                if last>=0 and i==last: continue
                nd[(hmul(s,h),i)] += c
        dist=nd
    W=defaultdict(int)
    for (h,last),c in dist.items(): W[h]+=c
    allH=[(v,j,z) for v in range(81) for j in range(5) for z in range(3)]
    return [W.get(h,0) for h in allH]
NSL=32736
def pred(vals): return sum(NSL*math.exp(-w/NSL) for w in vals)
Hord=81*5*3
print("mod",mod,"zeta",zeta,"|H|",Hord,"N",NSL*Hord)
# candidate variants: f = (0,jf,zf) fixed letter; orbit s=(v0,j0,z0) with v0=1 (scaling symmetry)
best=[]
for jf,zf in [(0,0),(0,1),(1,0)]:
    for j0,z0 in [(1,0),(2,0),(1,1)]:
        orb=[(zp[i]*1 % 81 if False else 0,0,0) for i in range(0)]
        orb=[(enc(dec(zp[i])),j0,z0) for i in range(5)]  # placeholder replaced below
        orb=[(zp[i],j0,z0) for i in range(5)]  # v_i = zeta^i * 1
        S=[(0,0,0),(0,jf,zf)]+orb
        v=walk_vals(S)
        best.append((round(pred(v),1), jf,zf,j0,z0, round(min(v)/NSL,2), round(sorted(v)[len(v)//2]/NSL,2)))
best.sort()
for b in best: print("pred_holes=%s f=(0,%d,%d) orbit j0=%d z0=%d minW/N=%s medW/N=%s" % b)
print("uniform baseline for this H:", round(NSL*Hord*math.exp(-423263232/(NSL*Hord)),1))
