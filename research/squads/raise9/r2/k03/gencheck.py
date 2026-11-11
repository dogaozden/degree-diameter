import random, sys
p=31
def canon(m):
    a,b,c,d=m
    f = a if a else c
    if f > (p-1)//2: a,b,c,d=(-a)%p,(-b)%p,(-c)%p,(-d)%p
    return (a,b,c,d)
def mul(x,y):
    a,b,c,d=x; e,f,g,h=y
    return canon(((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p))
def inv(x):
    a,b,c,d=x; return canon((d,(-b)%p,(-c)%p,a))
g=(0,p-1,1,12)  # alpha conj matrix from haar_big0 output: mat(0,30,1,12)
# check order 5 projectively
y=(1,0,0,1)
for i in range(1,6):
    y=mul(y,g)
print("g^5 =", y)
ginv=inv(canon(g))
def alpha(x): return mul(mul(canon(g),x),ginv)
def closure(gens):
    S={(1,0,0,1)}; frontier=[(1,0,0,1)]
    while frontier:
        nf=[]
        for x in frontier:
            for s in gens:
                y=mul(x,s)
                if y not in S: S.add(y); nf.append(y)
        frontier=nf
    return len(S)
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
sizes=[]
for t in range(8):
    while True:
        x=canon(tuple(random.randrange(p) for _ in range(4)))
        if (x[0]*x[3]-x[1]*x[2])%p!=1: continue
        break
    o=[x]
    for i in range(4): o.append(alpha(o[-1]))
    if alpha(o[-1])!=x: print("bad orbit"); continue
    sizes.append(closure(o))
print("generated subgroup sizes of random 5-orbits:", sizes)
