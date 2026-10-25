# Lemma 6.4 table of POLISHED.md: -c a non-square and G(a,b)=(c0 a+c1 b)(a^2+c b^2)-b^3 zero-free on F^2\{0}.
# F_9 = F_3[i], i^2=-1, encoded a0+a1*i -> a0+3*a1 (so i=3, 1+i=4, 2i=6).
from gf import make
tab={3:(1,1,2),5:(2,1,0),7:(1,1,0),9:(4,3,6),11:(1,1,3),13:(2,1,1)}
for q,(c,c0,c1) in tab.items():
    F=make(q)
    if q==9: assert F.m(3,3)==F.neg[1]
    G=lambda a,b: F.sub(F.m(F.a(F.m(c0,a),F.m(c1,b)),F.a(F.m(a,a),F.m(c,b,b))),F.m(b,b,b))
    zeros=[(a,b) for a in range(q) for b in range(q) if (a,b)!=(0,0) and G(a,b)==0]
    print("q=%d: -c non-square: %s; zeros of G: %s"%(q,F.chi(F.neg[c])==-1,zeros))
