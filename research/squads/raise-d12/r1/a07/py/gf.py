# GF(32) with x^5+x^2+1 (as in haar_sym's poly), SL(2,32) helpers, Frobenius x->x^2
import random
POLY = 0b100101  # x^5+x^2+1
def gmul(a,b):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a&32: a^=POLY
    return r
MUL=[[gmul(a,b) for b in range(32)] for a in range(32)]
def frob(a): return MUL[a][a]
def mm(A,B):
    a,b,c,d=A; e,f,g,h=B
    return (MUL[a][e]^MUL[b][g], MUL[a][f]^MUL[b][h], MUL[c][e]^MUL[d][g], MUL[c][f]^MUL[d][h])
def closure(gens, cap=40000):
    I=(1,0,0,1); seen={I}; frontier=[I]
    while frontier:
        nf=[]
        for x in frontier:
            for g in gens:
                y=mm(x,g)
                if y not in seen:
                    seen.add(y); nf.append(y)
                    if len(seen)>cap: return len(seen)
        frontier=nf
    return len(seen)
def rand_sl(rng):
    while True:
        a,b,c,d=[rng.randrange(32) for _ in range(4)]
        if MUL[a][d]^MUL[b][c]==1: return (a,b,c,d)
