# Per-(class, copy) labellings: hub (t,Y) sits at mu_{Y,c}(t) in copy c, every mu a collineation (all transfers
# geometric). Every pass through class Y from c to d applies mu_{Y,d} mu_{Y,c}^-1. Count distinct radius-4 and
# radius-2 words for the best (X, c') pair; reference = one radius-4 centre (as in Theorem 3.5's proof).
import sys
from myroutes import wiring
def red_prepend(w,s):
    if w and w[0]==(s[0],-s[1]): return w[1:]
    return (s,)+w
def routes_pc(pattern,X,cp,maxlen=7):
    C,meets=wiring(pattern); bar=X[0]; best={}
    def rec(c,g,used,p,typ):
        for a in range(0,maxlen-1-used-2*p+1):
            L=1+used+a+2*p
            if L>maxlen: break
            t2=typ^(a&1)
            if c==cp and t2==0:
                if best.get(g,-1)<used+a: best[g]=used+a
            if L+2>maxlen: continue
            for Y in meets[c]:
                same=(Y[0]==bar)
                if same and t2!=0: continue
                if (not same) and t2!=1: continue
                for d in C[Y]:
                    if d==c: continue
                    g2=red_prepend(g,((Y,c),-1)); g2=red_prepend(g2,((Y,d),1))
                    rec(d,g2,used+a,p+1,t2)
    for c1 in C[X]: rec(c1,(((X,c1),1),),0,0,0)
    return best
q=int(sys.argv[1]); pattern=sys.argv[2]
C,meets=wiring(pattern)
res=[]
for X in C:
    for cp in range(5*len(pattern)):
        if cp in C[X]: continue
        b=routes_pc(pattern,X,cp)
        m4=sum(1 for v in b.values() if v==4); m2=sum(1 for v in b.values() if v==2)
        res.append((q**5-(m4-1)*q**4-m2*q*q,X,cp,m4,m2))
res.sort(reverse=True)
print("q=%d %s per-(class,copy) geometric labellings: best pair X=%s c'=%d: %d radius-4 centres, %d radius-2; bound %d"%((q,pattern)+res[0][1:]+(res[0][0],)))
