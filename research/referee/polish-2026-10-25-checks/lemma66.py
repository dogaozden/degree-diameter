# Lemma 6.6 (a),(b),(d) and Lemma 6.7 of POLISHED.md, checked symbolically (sympy).
import sympy as sp
x1,x2,x3,x4,x5,x6,c,al,be,s,t=sp.symbols('x1:7 c alpha beta s t')
x=sp.Matrix([x1,x2,x3,x4,x5,x6])
def J(v,al=al,be=be):
    v1,v2,v3,v4,v5,v6=v
    return sp.Matrix([-be*v3+al*v4-v6, v5, -c*v4-be*v5, v3+be*v2, -c*v2, c*v1+al*be*v2+al*v3+c*be*v4+be**2*v5])
def full(v): v1,v2,v3,v4,v5,v6=v; return [-c*v4-al*v2-be*v5,v1,v2,v3,v4,v5,v6]
def Q7(X): return X[0]*X[4]+X[1]*X[5]+X[2]*X[6]-X[3]**2
def Qzf(v): return sp.expand(Q7(full(v)))
text=x1*x5+x2*x6-x3**2-c*x4**2-al*x2*x4-be*x4*x5
print("Q_z formula as printed:",sp.expand(Qzf(x)-text)==0)
Jx=J(x)
print("(a) J^2=-c:",sp.simplify(J(Jx)+c*x)==sp.zeros(6,1))
print("(a) Q(Jx)=cQ(x):",sp.expand(Qzf(Jx)-c*Qzf(x))==0)
Bz=lambda u,w: sp.expand(Qzf(u+w)-Qzf(u)-Qzf(w))
print("(a) B(x,Jx)=0:",Bz(x,Jx)==0)
X=full(x); Y=full(Jx)
p=lambda i,j: sp.expand(X[i]*Y[j]-X[j]*Y[i])
diffs=[p(1,2)-p(3,4),p(5,4)-p(3,2),p(2,0)-p(3,5),p(6,5)-p(3,0),p(0,1)-p(3,6),p(4,6)-p(3,1)]
print("(b) differences = Q_z*(1,0,0,-c,alpha,-beta):",[sp.expand(d-k*Qzf(x))==0 for d,k in zip(diffs,[1,0,0,-c,al,-be])])
J0=J(x,0,0); num=lambda v: v[1]*v[2]-v[3]*v[4]; den=lambda v: c*v[1]**2+v[4]**2
w=s*x+t*J0
print("(d):",sp.expand(num(w)-(s**2+c*t**2)*num(x))==0,sp.expand(den(w)-(s**2+c*t**2)*den(x))==0, "J_0 as printed:",list(J0)==[-x6,x5,-c*x4,x3,-c*x2,c*x1])
p2,p3,p4,p5,gam=sp.symbols('p2 p3 p4 p5 gamma')
Th=c*p2**2+p5**2; alpha=-(c*p2+gam*p5)/Th; beta=(gam*p2-p5)/Th
X2=gam*p2-p5; X3=gam*p3+c*p4+beta*p5; X4=gam*p4-p3-beta*p2; X5=gam*p5+c*p2
print("Lemma 6.7 solve:",sp.simplify(alpha*p2+beta*p5+1)==0,sp.simplify(-alpha*p5+c*beta*p2-gam)==0)
print("Lemma 6.7 identity:",sp.simplify((X2*X3-X4*X5)/(c*X2**2+X5**2)+beta**3/(alpha**2+c*beta**2)-(p2*p3-p4*p5+beta*p2**2)/Th)==0)
