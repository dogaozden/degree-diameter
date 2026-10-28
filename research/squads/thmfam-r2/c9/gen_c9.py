"""Generators for the (-1,-3) quaternion Haar graph on PGL(2,q).
usage: gen_c9.py p q [units]
 - S = elements of Z<1,i,j,k> of norm p up to sign (default) or up to units {+-1,+-i} (flag 'units')
 - psi: i->I, j->J, k->IJ with I=[[0,-1],[1,0]], J=[[x,y],[y,-x]], x^2+y^2=-3 mod q
 - prints generator lines "a b c d 0" to stdout; writes targets (psi(1), psi(i), psi(j), psi(k)) to targets_p_q.txt
"""
import sys, math
p=int(sys.argv[1]); q=int(sys.argv[2]); units = len(sys.argv)>3 and sys.argv[3]=='units'
def norm(a): return a[0]**2+a[1]**2+3*a[2]**2+3*a[3]**2
def elems(n):
    r=math.isqrt(n); out=[]
    for a0 in range(-r,r+1):
        for a1 in range(-r,r+1):
            s=n-a0*a0-a1*a1
            if s<0: continue
            for a2 in range(-math.isqrt(s//3)-1, math.isqrt(s//3)+2):
                t=s-3*a2*a2
                if t<0 or t%3: continue
                u=t//3; a3=math.isqrt(u)
                if a3*a3==u:
                    out.append((a0,a1,a2,a3))
                    if a3: out.append((a0,a1,a2,-a3))
    return out
E=[a for a in elems(p) if norm(a)==p]
# up to sign
cls=[]; seen=set()
for a in E:
    if a in seen: continue
    neg=tuple(-x for x in a); seen.add(a); seen.add(neg); cls.append(a)
if units:
    # quotient by {+-1,+-i}: multiply by i: (a0,a1,a2,a3)*i = (-a1, a0, -a3, a2)?? compute via product below
    def mul(x,y):
        # quaternion product in basis 1,i,j,k with i^2=-1, j^2=-3, k=ij, ji=-k
        a0,a1,a2,a3=x; b0,b1,b2,b3=y
        # (a0+a1 i+a2 j+a3 k)(b0+b1 i+b2 j+b3 k), using i^2=-1,j^2=-3,k^2=-3,ij=k,ji=-k,ik=-3j? compute: ik=i(ij)=-j, ki=(ij)i=-(i j)... use matrices instead
        return None
    # use matrix-free rule: i*x, x*i with the exact multiplication table
    def qmul(x,y):
        a0,a1,a2,a3=x; b0,b1,b2,b3=y
        # table: 1*1=1, i*i=-1, j*j=-3, k*k=-3, ij=k, ji=-k, ik=i*ij=-j (i*k=i*(ij)=i^2 j=-j), ki=(ij)i=i(ji)=-i(k)... compute directly:
        # ki = (ij)i = i(ji) = i(-ij) = -i^2 j = j ; ik=-j ; jk=j(ij)=(ji)j=-(ij)j=-i j^2=3i ; kj=(ij)j=i j^2=-3i
        # k*k = (ij)(ij) = i(ji)j = -i(ij)j = -i^2 j^2 = -(-1)(-3) = -3
        r0 = a0*b0 - a1*b1 - 3*a2*b2 - 3*a3*b3
        r1 = a0*b1 + a1*b0 + a2*b3*(3) + a3*b2*(-3)   # j k=3i, k j=-3i
        r2 = a0*b2 + a2*b0 + a1*b3*(-1) + a3*b1*(1)    # i k=-j, k i=j
        r3 = a0*b3 + a3*b0 + a1*b2 - a2*b1            # ij=k, ji=-k
        return (r0,r1,r2,r3)
    # check k*k = -3 and i*j = k
    assert qmul((0,1,0,0),(0,0,1,0))==(0,0,0,1) and qmul((0,0,0,1),(0,0,0,1))==(-3,0,0,0)
    cls2=[]; seen=set()
    for a in cls:
        if a in seen: continue
        orb={a}
        for u in [(1,0,0,0),(-1,0,0,0),(0,1,0,0),(0,-1,0,0)]:
            orb.add(qmul(a,u)); 
        for o in orb: seen.add(o); seen.add(tuple(-x for x in o))
        cls2.append(a)
    cls=cls2
# splitting over F_q
def inv(x): return pow(x,q-2,q)
I=((0,q-1),(1,0))
x=y=None
for xx in range(q):
    yy2=(-3-xx*xx)%q
    yy=next((yv for yv in range(q) if yv*yv%q==yy2),None)
    if yy is not None: x,y=xx,yy; break
assert x is not None, "no J"
J=((x,y),(y,(-x)%q))
def mm(A,B): return tuple(tuple(sum(A[r][t]*B[t][c] for t in range(2))%q for c in range(2)) for r in range(2))
def add(A,B,s=1): return tuple(tuple((A[r][c]+s*B[r][c])%q for c in range(2)) for r in range(2))
def scal(s,A): return tuple(tuple(s*A[r][c]%q for c in range(2)) for r in range(2))
IJ=mm(I,J)
assert mm(I,I)==((q-1,0),(0,q-1)) and mm(J,J)==scal((-3)%q,((1,0),(0,1))) and add(mm(I,J),mm(J,I))==((0,0),(0,0))
Id=((1,0),(0,1))
def psi(a):
    M=scal(a[0]%q,Id)
    M=add(M,I,a[1]); M=add(M,J,a[2]); M=add(M,IJ,a[3])
    return M
def pn(M):
    # projective normal form
    flat=[M[0][0],M[0][1],M[1][0],M[1][1]]
    f=next(v for v in flat if v%q); s=inv(f)
    return tuple(v*s%q for v in flat)
imgs={}
bad=0
for a in cls:
    M=psi(a); det=(M[0][0]*M[1][1]-M[0][1]*M[1][0])%q
    if det!=norm(a)%q: bad+=1
    key=pn(M)
    if key in imgs: print("#COLLISION",a,imgs[key],file=sys.stderr)
    imgs.setdefault(key,a)
    print(" ".join(str(v) for v in (M[0][0],M[0][1],M[1][0],M[1][1]))+" 0")
print("#classes",len(cls),"distinct_images",len(imgs),"det_mismatch",bad,"p",p,"q",q,"units" if units else "sign",file=sys.stderr)
with open(f"targets_{p}_{q}.txt","w") as f:
    for a in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]:
        M=psi(a); f.write(" ".join(str(v) for v in (M[0][0],M[0][1],M[1][0],M[1][1]))+"\n")
