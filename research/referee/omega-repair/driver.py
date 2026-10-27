# Build a twisted labelling P_c = a_c, L_c = b_c (independent random collineations), run omg (BFS from a hub),
# and compare the reached target-colour vertices of c' with the union of route balls from myroutes.py.
import sys, random, subprocess, numpy as np, time
from collin import Hex
from myroutes import routes, wiring
q=int(sys.argv[1]); pattern=sys.argv[2]; seed=int(sys.argv[3]); Xs=sys.argv[4]; cp=int(sys.argv[5]); row=int(sys.argv[6])
X=(Xs[0],int(Xs[1:]))
H=Hex(q); R=random.Random(seed); N=H.N; C=5*len(pattern)
t0=time.time()
a=[];b=[]
ident=(np.arange(N),np.arange(N))
for c in range(C):
    if seed==-1: a.append(ident); b.append(ident); continue
    if seed<=-2:
        _, (pp,lp) = H.random_collineation(R, nfac=8); a.append((pp,lp)); b.append((pp,lp)); continue
    _, (pp,lp) = H.random_collineation(R, nfac=8); a.append((pp,lp))
    _, (pp,lp) = H.random_collineation(R, nfac=8); b.append((pp,lp))
print("generated %d collineations, each checked line by line (%.0fs)"%(2*C,time.time()-t0),flush=True)
lab="lab_q%d_%s_%d.bin"%(q,pattern,seed)
with open(lab,"wb") as f:
    np.array([C,N],dtype=np.int32).tofile(f)
    for c in range(C):
        a[c][0].astype(np.int32).tofile(f); b[c][1].astype(np.int32).tofile(f)
out="reached_q%d.txt"%q
r=subprocess.run(["./omg","hex_q%d.txt"%q,lab,pattern,X[0],str(X[1]),str(row),str(cp),out],capture_output=True,text=True)
print(r.stdout,r.stderr)
reached=set(int(x) for x in open(out))
def inv(p): r=np.empty_like(p); r[p]=np.arange(len(p)); return r
def comp(f,g): return (f[0][g[0]], f[1][g[1]])
def cinv(f): return (inv(f[0]),inv(f[1]))
mu=[comp(cinv(a[c]),b[c]) if X[0]=='u' else comp(cinv(b[c]),a[c]) for c in range(C)]
words=routes(pattern,X,cp)
typ=0 if X[0]=='u' else 1          # 0 points, 1 lines
def apply_word(w,x):
    for (c,e) in reversed(w):
        f=mu[c] if e==1 else cinv(mu[c])
        x=int(f[typ][x])
    return x
def ball(z,r,ty):
    seen={(ty,z)}; fr=[(ty,z)]
    for _ in range(r):
        nf=[]
        for (t,x) in fr:
            nb=[(1,l) for l in H.ptlines[x]] if t==0 else [(0,int(p)) for p in H.lines[x]]
            for y in nb:
                if y not in seen: seen.add(y); nf.append(y)
        fr=nf
    return {x for (t,x) in seen if t==ty}
pred=set()
for w,rad in words.items():
    z=apply_word(w,row)
    pred|=ball(z,rad,typ)
fin=a[cp] if X[0]=='u' else b[cp]
pred_orig={int(fin[typ][x]) for x in pred}
print("route words: %d (radius 4: %d, radius 2: %d, radius 0: %d)"%(len(words),sum(1 for v in words.values() if v==4),sum(1 for v in words.values() if v==2),sum(1 for v in words.values() if v==0)))
print("predicted union %d, BFS reached %d, equal: %s, reached minus predicted: %d"%(len(pred_orig),len(reached),pred_orig==reached,len(reached-pred_orig)))
print("far target-colour vertices of copy %d: %d"%(cp,N-len(reached)))
