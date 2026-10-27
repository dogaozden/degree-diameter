# Split octonions as Zorn vector matrices (a,u,v,b), a,b in F, u,v in F^3.
# xy = (aa'+u.v', a u' + b' u - v x v', a' v + b v' + u x u', bb' + v.u'),  N(x) = ab - u.v
import numpy as np
from gf import make_gf
class Oct:
    def __init__(s,q):
        s.q=q; s.add,s.mul,s.neg,s.inv=make_gf(q)
    def A(s,*xs):
        r=xs[0]
        for x in xs[1:]: r=s.add[r,x]
        return r
    def M(s,a,b): return s.mul[a,b]
    def sub(s,a,b): return s.add[a,s.neg[b]]
    def dot(s,u,v): return s.A(s.M(u[0],v[0]),s.M(u[1],v[1]),s.M(u[2],v[2]))
    def cross(s,u,v):
        return [s.sub(s.M(u[1],v[2]),s.M(u[2],v[1])), s.sub(s.M(u[2],v[0]),s.M(u[0],v[2])), s.sub(s.M(u[0],v[1]),s.M(u[1],v[0]))]
    def prod(s,x,y):
        a,u,v,b=x[0],x[1:4],x[4:7],x[7]
        a2,u2,v2,b2=y[0],y[1:4],y[4:7],y[7]
        c=s.add[s.M(a,a2),s.dot(u,v2)]
        cv=s.cross(v,v2); cu=s.cross(u,u2)
        U=[s.sub(s.add[s.M(a,u2[i]),s.M(b2,u[i])],cv[i]) for i in range(3)]
        V=[s.A(s.M(a2,v[i]),s.M(b,v2[i]),cu[i]) for i in range(3)]
        d=s.add[s.M(b,b2),s.dot(v,u2)]
        return [c]+U+V+[d]
    def norm(s,x): return s.sub(s.M(x[0],x[7]),s.dot(x[1:4],x[4:7]))
if __name__=="__main__":
    import random
    for q in (7,8,9,3,4,5):
        o=Oct(q); R=random.Random(1)
        for _ in range(3000):
            x=[R.randrange(q) for _ in range(8)]; y=[R.randrange(q) for _ in range(8)]
            assert o.norm(o.prod(x,y))==o.M(o.norm(x),o.norm(y))
        # alternativity x(xy) = (xx)y
        for _ in range(500):
            x=[R.randrange(q) for _ in range(8)]; y=[R.randrange(q) for _ in range(8)]
            assert o.prod(x,o.prod(x,y))==o.prod(o.prod(x,x),y)
        print("q=%d: N(xy)=N(x)N(y) and x(xy)=(xx)y on random samples"%q)
