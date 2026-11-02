import sys
# GF(32), x^5+x^2+1
def gmul(a,b):
    r=0
    for i in range(5):
        if b>>i&1: r^=a<<i
    for i in range(9,4,-1):
        if r>>i&1: r^=0x25<<(i-5)
    return r
def mm(A,B):
    a,b,c,d=A; e,f,g,h=B
    return (gmul(a,e)^gmul(b,g), gmul(a,f)^gmul(b,h), gmul(c,e)^gmul(d,g), gmul(c,f)^gmul(d,h))
def closure(gens, mul, e):
    seen={e}; frontier=[e]
    while frontier:
        nf=[]
        for x in frontier:
            for g in gens:
                y=mul(x,g)
                if y not in seen:
                    seen.add(y); nf.append(y)
        frontier=nf
    return seen
rows=[l.split() for l in open(sys.argv[1]) if not l.startswith('#')]
rows=[tuple(int(v) for v in r) for r in rows]
sl=[(r[0],r[1],r[2],r[3]) for r in rows]
hh=[(r[4],r[5]) for r in rows]
print("SL gens", sl)
Gsl=closure(sl, mm, (1,0,0,1))
print("SL-projection order", len(Gsl), "of 32736")
# H = Z191 x|_r Z5 with r of order 5
P=191
r=None
for t in range(2,P):
    x=pow(t,38,P)
    if x!=1: r=x; break
def hmul(x,y):
    a1,j1=x; a2,j2=y
    return ((a1+pow(r,j1,P)*a2)%P,(j1+j2)%5)
Gh=closure(hh, hmul, (0,0))
print("H-projection order", len(Gh), "of 955")
print("H gens", hh)
