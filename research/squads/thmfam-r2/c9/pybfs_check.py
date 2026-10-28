"""Independent check: BFS on the Haar graph over PGL(2,q) with python sets (small q only)."""
import sys, subprocess, collections
p,q=int(sys.argv[1]),int(sys.argv[2])
gens=[tuple(map(int,l.split()[:4])) for l in open(f'/home/user/degree-diameter/research/squads/thmfam-r2/c9/work/gens_units_{p}_{q}.txt') if l.strip()]
def pn(v):
    f=next(t for t in v if t); s=pow(f,q-2,q); return tuple(t*s%q for t in v)
def mul(A,B): return (( A[0]*B[0]+A[1]*B[2])%q,(A[0]*B[1]+A[1]*B[3])%q,(A[2]*B[0]+A[3]*B[2])%q,(A[2]*B[1]+A[3]*B[3])%q)
def inv_adj(A): return (A[3],(-A[1])%q,(-A[2])%q,A[0])
e=pn((1,0,0,1))
dist={('A',e):0}; frontier=[('A',e)]; ecc={}
def bfs(start):
    d={start:0}; fr=[start]; k=0
    while fr:
        nxt=[]
        for side,g in fr:
            if side=='A':
                for s in gens:
                    h=pn(mul(s,g)); key=('B',h)
                    if key not in d: d[key]=d[(side,g)]+1; nxt.append(key)
            else:
                for s in gens:
                    h=pn(mul(inv_adj(s),g)); key=('A',h)
                    if key not in d: d[key]=d[(side,g)]+1; nxt.append(key)
        fr=nxt
    return d
dA=bfs(('A',e)); dB=bfs(('B',e))
print("p",p,"q",q,"compA",len(dA),"ecc_A",max(dA.values()),"ecc_B",max(dB.values()))
I=pn((0,q-1,1,0)) if False else None
# psi(i) as normal form from targets file
t=[tuple(map(int,l.split())) for l in open(f'/home/user/degree-diameter/research/squads/thmfam-r2/c9/work/targets_{p}_{q}.txt')]
print("d_A(psi i) python:", dA.get(('A',pn(t[1])),-1), " targets file says it is", t[1])
