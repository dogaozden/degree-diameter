# Lemma 3.1 from distance-regularity: the incidence graph of a generalized hexagon of order (q,q)
# is distance-regular with intersection array {q+1,q,q,q,q,q; 1,1,1,1,1,q+1}.
# p[d][i][j] = #{x : d(z,x)=i, d(t,x)=j} for d(z,t)=d. Computed from the intersection matrix.
import sys
from fractions import Fraction
def inter(q):
    D=6
    b=[q+1,q,q,q,q,q,0]; c=[0,1,1,1,1,1,q+1]; a=[0]*7
    k=q+1
    # distance matrices A_i as polynomials: use the standard recurrence on the "intersection algebra"
    # Represent A_i by its column of p^h_{i,j} via p^h_{1,j}: A_1 A_j = b_{j-1} A_{j-1} + a_j A_j + c_{j+1} A_{j+1}
    # compute p^h_{ij} by p^h_{i+1,j} = (sum_l p^h_{i,l} p^l_{1,j}... ) use matrix L_j (j-th intersection matrix)
    # L1[l][m] = p^m_{1,l}? Simpler: build B = tridiagonal matrix with B[i][i-1]=c_i, B[i][i]=a_i, B[i][i+1]=b_i.
    n=D+1
    B=[[0]*n for _ in range(n)]
    for i in range(n):
        if i>0: B[i][i-1]=b[i-1]   # column convention: (A_1 A_i) = b_{i-1}A_{i-1}+a_iA_i+c_{i+1}A_{i+1}
        B[i][i]=a[i]
        if i<n-1: B[i][i+1]=c[i+1]
    # p^h_{ij}: express A_i A_j = sum_h p^h_{ij} A_h. Represent A_i as vector over basis A_h (unit vectors),
    # and multiplication by A_1 is the matrix M with M[h][i] = coefficient of A_h in A_1A_i.
    M=[[0]*n for _ in range(n)]
    for i in range(n):
        if i>0: M[i-1][i]=b[i-1]
        M[i][i]=a[i]
        if i<n-1: M[i+1][i]=c[i+1]
    # A_i as polynomial v_i(A_1): v_0 = 1, A_1 v_i = b_{i-1} v_{i-1} + a_i v_i + c_{i+1} v_{i+1}
    # Products: A_i A_j vector = v_i(M) e_j
    import itertools
    def matmul(X,Y): return [[sum(X[r][s]*Y[s][cc] for s in range(n)) for cc in range(n)] for r in range(n)]
    I=[[Fraction(int(r==cc)) for cc in range(n)] for r in range(n)]
    Mf=[[Fraction(x) for x in row] for row in M]
    V=[I, Mf]
    for i in range(1,n-1):
        Vn=matmul(Mf,V[i])
        Vn=[[Vn[r][cc]-b[i-1]*V[i-1][r][cc]-a[i]*V[i][r][cc] for cc in range(n)] for r in range(n)]
        Vn=[[x/c[i+1] for x in row] for row in Vn]
        V.append(Vn)
    # p^h_{ij} = (V[i] e_j)[h]
    p=[[[V[i][h][j] for j in range(n)] for i in range(n)] for h in range(n)]
    return p
for q in [2,3,4,5,7,8,9,11,13]:
    p=inter(q)
    # sanity: p^0_{ii} = k_i
    ks=[p[0][i][i] for i in range(7)]
    assert sum(ks)==2*(q**6-1)//(q-1), (q,ks)
    out=[]
    for R in range(5):
        vals={d:int(sum(p[d][i][6] for i in range(R+1))) for d in range(7) if (d%2)==(R%2) or True}
        # only meaningful parity: centre z of same type as t iff d even
        out.append((R,{d:v for d,v in vals.items() if (d%2==0)==(R%2==0)}))
    print("q=%d k_i=%s"%(q,[int(x) for x in ks]))
    for R,v in out: print("   |B(z,%d) ∩ opp(t)| by d(t,z):"%R, v)
