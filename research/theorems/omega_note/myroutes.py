# Independent route enumeration for Gomez's wiring, reading 2, twisted labelling in normal form.
# Source hub of class X (bar beta). Same-bar hubs sit on the same vertex index in every copy;
# opposite-bar hubs sit on mu_c(m) in copy c, so a pass through one from copy c to d applies mu_d mu_c^-1.
# Walk: hub -> its vertex in c1, then segments inside copies (length a_i) and passes (2 edges each).
# Total length 1 + sum a_i + 2*passes <= 7, ends in copy c' at a vertex of the source-bar colour.
# Endpoint lies in B(g(x0), sum a_i), g the reduced word. Record max radius per reduced word.
import sys
from itertools import product
def wiring(pattern):
    # classes: ('u',k) unbarred, ('b',k) barred. copies 5B+i.
    C={}
    for k in range(5):
        C[('u',k)]=[]; C[('b',k)]=[]
    for B,T in enumerate(pattern):
        for k in range(5):
            if T=='a':
                C[('u',k)]+= [5*B+(k-1)%5, 5*B+(k+1)%5]
                C[('b',k)]+= [5*B+(k+2)%5, 5*B+(k+3)%5]
            else:
                C[('u',k)]+= [5*B+(k+3)%5, 5*B+(k+4)%5]
                C[('b',k)]+= [5*B+(k-1)%5, 5*B+(k+1)%5]
    meets={c:[] for c in range(5*len(pattern))}
    for Y,cs in C.items():
        assert len(set(cs))==len(cs)
        for c in cs: meets[c].append(Y)
    for c in meets: assert len(meets[c])==4
    return C,meets
def mul(d,c,g):
    # word for mu_d mu_c^{-1} g, words are tuples of (copy, +-1), leftmost applied last
    w=list(g)
    pre=[(d,1),(c,-1)]
    for s in reversed(pre):
        if w and w[0]==(s[0],-s[1]): w.pop(0)
        else: w.insert(0,s)
    return tuple(w)
def routes(pattern,X,cp,maxlen=7):
    C,meets=wiring(pattern)
    bar=X[0]
    best={}
    # state: copy c, word g, used segment total, passes p, type of current vertex at segment start (0 = source colour)
    def rec(c,g,used,p,typ):
        # choose segment length a
        for a in range(0, maxlen-1-used-2*p+1):
            L=1+used+a+2*p
            if L>maxlen: break
            t2=typ^(a&1)
            if c==cp and t2==0:
                r=used+a
                if best.get(g,-1)<r: best[g]=r
            if L+2>maxlen: continue
            for Y in meets[c]:
                same=(Y[0]==bar)
                if same and t2!=0: continue
                if (not same) and t2!=1: continue
                for d in C[Y]:
                    if d==c: continue
                    rec(d, g if same else mul(d,c,g), used+a, p+1, t2)
    for c1 in C[X]:
        rec(c1,(),0,0,0)
    return best
def summary(best):
    m={4:0,2:0,0:0}
    ident=best.get((),None)
    for g,r in best.items(): m[r]=m.get(r,0)+1
    return m,ident
if __name__=="__main__":
    q=int(sys.argv[1]); pattern=sys.argv[2]
    C,meets=wiring(pattern)
    res=[]
    for X in C:
        for cp in range(5*len(pattern)):
            if cp in C[X]: continue
            best=routes(pattern,X,cp)
            m,ident=summary(best)
            tw4=m[4]-(1 if ident==4 else 0)
            # bound: identity ball misses opp(t); other radius-4 words <= q^4, radius-2 <= q^2, radius-0 <= 1
            m0=m.get(0,0)-(1 if ident==0 else 0)
            bound=q**5-tw4*q**4-m[2]*q*q-m0
            res.append((bound,X,cp,tw4,m[2],m.get(0,0),ident,sorted(set(best.values()))))
    res.sort(reverse=True)
    b=res[0]
    print("q=%d %s: best pair X=%s c'=%d: twisted r4=%d m2=%d m0=%d identity radius=%s  bound=%d"%(q,pattern,b[1],b[2],b[3],b[4],b[5],b[6],b[0]))
    st=[r for r in res if r[3]==len(pattern)]
    if st:
        for bar in 'ub':
            s=[r for r in st if r[1][0]==bar]
            print("   starved pairs (exactly alpha twisted r4) with X %s: %d, m2 range %s"%('unbarred' if bar=='u' else 'barred',len(s),(min(r[4] for r in s),max(r[4] for r in s)) if s else None))
    print("   min twisted r4 over all pairs: %d"%min(r[3] for r in res))
