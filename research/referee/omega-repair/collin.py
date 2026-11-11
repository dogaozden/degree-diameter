# Collineations of H(q) (octonion model): products of SL(3,q) maps (a,u,v) -> (a, Au, A^-T v) and
# Siegel maps x -> x + B(x,u)v - B(x,v)u along hexagon lines <u,v>. Every element produced is checked
# line by line (each line must map to a line) before it is used.
import numpy as np, random
from gf import make_gf
class Hex:
    def __init__(s,q):
        d=np.load("hex_q%d.npz"%q); s.q=q
        s.pts=d['pts']; s.lines=d['lines']; s.N=len(s.pts)
        s.add,s.mul,s.neg,s.inv=make_gf(q)
        w=q**np.arange(6,-1,-1)
        s.w=w
        s.code=np.full(q**7,-1,dtype=np.int64); s.code[s.pts@w]=np.arange(s.N)
        s.lkey={tuple(L):i for i,L in enumerate(s.lines.tolist())}
        s.ptlines=[[] for _ in range(s.N)]
        for i,L in enumerate(s.lines.tolist()):
            for p in L: s.ptlines[p].append(i)
    def matvec_all(s,M):
        out=np.zeros_like(s.pts)
        for i in range(7):
            acc=np.zeros(s.N,dtype=np.int64)
            for j in range(7):
                if M[i][j]: acc=s.add[acc, s.mul[M[i][j], s.pts[:,j]]]
            out[:,i]=acc
        return out
    def normalize_rows(s,X):
        nz=(X!=0); first=np.argmax(nz,axis=1)
        lead=X[np.arange(len(X)),first]
        assert (lead!=0).all()
        return s.mul[s.inv[lead][:,None], X]
    def perm_of(s,M):
        Y=s.normalize_rows(s.matvec_all(M))
        pp=s.code[Y@s.w]
        assert (pp>=0).all(), "image not a point"
        assert len(set(pp.tolist()))==s.N
        img=np.sort(pp[s.lines],axis=1)
        lp=np.array([s.lkey.get(tuple(r),-1) for r in img.tolist()])
        if (lp<0).any(): return None
        return pp, lp
    # field helpers on scalars
    def B(s,x,y):  # polar form of N on pure coords (a,u,v): N = -a^2 - u.v ; B = -2aa' - u.v' - u'.v
        A,M,n=s.add,s.mul,s.neg
        r=n[s.add[M[x[0],y[0]],M[x[0],y[0]]]]      # -2aa'
        for i in range(3):
            r=A[r, n[M[x[1+i],y[4+i]]]]
            r=A[r, n[M[y[1+i],x[4+i]]]]
        return int(r)
    def siegel(s,li):
        L=s.lines[li]; u=s.pts[L[0]].tolist(); v=s.pts[L[1]].tolist()
        M=[[int(i==j) for j in range(7)] for i in range(7)]
        # column j: e_j + B(e_j,u) v - B(e_j,v) u
        for j in range(7):
            e=[0]*7; e[j]=1
            bu=s.B(e,u); bv=s.B(e,v)
            for i in range(7):
                M[i][j]=int(s.add[s.add[M[i][j], s.mul[bu,v[i]]], s.neg[s.mul[bv,u[i]]]])
        return M
    def sl3(s,R,n=6):
        A=[[int(i==j) for j in range(3)] for i in range(3)]
        Ait=[[int(i==j) for j in range(3)] for i in range(3)]   # A^{-T}
        for _ in range(n):
            i,j=R.sample(range(3),2); lam=R.randrange(1,s.q)
            # A <- E_ij(lam) A ; A^{-T} <- E_ji(-lam) A^{-T}
            A[i]=[int(s.add[A[i][k], s.mul[lam,A[j][k]]]) for k in range(3)]
            Ait[j]=[int(s.add[Ait[j][k], s.mul[s.neg[lam],Ait[i][k]]]) for k in range(3)]
        M=[[0]*7 for _ in range(7)]; M[0][0]=1
        for i in range(3):
            for j in range(3):
                M[1+i][1+j]=A[i][j]; M[4+i][4+j]=Ait[i][j]
        return M
    def matmul(s,X,Y):
        return [[s._dot([X[i][k] for k in range(7)],[Y[k][j] for k in range(7)]) for j in range(7)] for i in range(7)]
    def _dot(s,a,b):
        r=0
        for x,y in zip(a,b): r=s.add[r,s.mul[x,y]]
        return int(r)
    def random_collineation(s,R,nfac=6):
        M=[[int(i==j) for j in range(7)] for i in range(7)]
        for t in range(nfac):
            G=s.sl3(R) if t%2==0 else s.siegel(R.randrange(s.N))
            M=s.matmul(G,M)
        res=s.perm_of(M)
        assert res is not None, "product failed the line check"
        return M,res
if __name__=="__main__":
    import sys
    q=int(sys.argv[1]); H=Hex(q); R=random.Random(5)
    ok_s=sum(H.perm_of(H.siegel(R.randrange(H.N))) is not None for _ in range(20))
    ok_l=sum(H.perm_of(H.sl3(R)) is not None for _ in range(20))
    print("q=%d: Siegel maps along hexagon lines that are collineations: %d/20; SL(3) maps: %d/20"%(q,ok_s,ok_l))
    # a Siegel map along a totally singular line that is NOT a hexagon line should fail
    M,(pp,lp)=H.random_collineation(R)
    fixed=int((pp==np.arange(H.N)).sum())
    print("random product of 6 generators: collineation, %d fixed points"%fixed)
