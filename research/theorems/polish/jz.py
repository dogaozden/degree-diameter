import sympy as sp
c,al,be=sp.symbols('c alpha beta')
x=sp.symbols('x1:7')
def full(v): return [-c*v[3]-al*v[1]-be*v[4]]+list(v)
def Q(X): return sp.expand(X[0]*X[4]+X[1]*X[5]+X[2]*X[6]-X[3]**2)
def J(v):
    x1,x2,x3,x4,x5,x6=v
    return [-be*x3+al*x4-x6, x5, -c*x4-be*x5, x3+be*x2, -c*x2, c*x1+al*be*x2+al*x3+c*be*x4+be**2*x5]
X=full(x); JX=full(J(x)); JJX=full(J(J(x)))
print('J^2=-c:', all(sp.expand(JJX[i]+c*X[i])==0 for i in range(7)))
print('Q(Jx)=cQ(x):', sp.expand(Q(JX)-c*Q(X))==0)
Bf=lambda U,V: sp.expand(Q([u+v for u,v in zip(U,V)])-Q(U)-Q(V))
print('B(x,Jx)=0:', Bf(X,JX)==0)
p=lambda i,j: X[i]*JX[j]-X[j]*JX[i]
diffs=[p(1,2)-p(3,4), p(5,4)-p(3,2), p(2,0)-p(3,5), p(6,5)-p(3,0), p(0,1)-p(3,6), p(4,6)-p(3,1)]
coef=[1,0,0,-c,al,-be]
print('Tits diffs:', [sp.expand(d-k*Q(X))==0 for d,k in zip(diffs,coef)])
J0=lambda v: [ -v[5], v[4], -c*v[3], v[2], -c*v[1], c*v[0]]
print('J0 matches:', all(sp.expand(a.subs({al:0,be:0})-b)==0 for a,b in zip(J(x),J0(x))))
num=lambda v: v[1]*v[2]-v[3]*v[4]; den=lambda v: c*v[1]**2+v[4]**2
s,t=sp.symbols('s t')
comb=[s*a+t*b for a,b in zip(x,J0(x))]
print('num scales:', sp.expand(num(comb)-(s**2+c*t**2)*num(x))==0, 'den scales:', sp.expand(den(comb)-(s**2+c*t**2)*den(x))==0)
# key identity: X(z) = gamma p - J_z p
p_=sp.symbols('p1:7')
gam=-al*p_[4]+c*be*p_[1]
Xz=[gam*a-b for a,b in zip(p_,J(p_))]
Theta=c*p_[1]**2+p_[4]**2
# impose alpha p2 + beta p5 = -1 by solving for alpha (p2 != 0 generic) and check identity
sol=sp.solve(sp.Eq(al*p_[1]+be*p_[4],-1),al)[0]
lhs=num(Xz)/den(Xz)+be**3/(al**2+c*be**2)
rhs=(p_[1]*p_[2]-p_[3]*p_[4]+be*p_[1]**2)/Theta
print('key identity:', sp.simplify((lhs-rhs).subs(al,sol))==0)
print('lambda(X)=0:', sp.simplify((full(Xz)[0]+c*Xz[3]).subs(al,sol))==0)
