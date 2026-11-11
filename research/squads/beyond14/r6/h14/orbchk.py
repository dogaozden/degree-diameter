import sys, math
def parse(fn):
    L=open(fn).read().split('\n')
    hdr=L[0].split(); d=int(hdr[0]); D=int(hdr[1]); n=int(hdr[hdr.index('n')+1]); 
    gens=[]
    for line in L[1:]:
        if 'mat(' not in line: continue
        a,b,c,dd=map(int,line[line.index('mat(')+4:line.index(')')].split(','))
        z=int(line.split('z=')[1])
        gens.append((a,b,c,dd,z))
    return d,n,gens
def mul(x,y,P,n):
    a,b,c,d,z=x; A,B,C,DD,Z=y
    return ((a*A+b*C)%P,(a*B+b*DD)%P,(c*A+d*C)%P,(c*B+d*DD)%P,(z+Z)%n)
def canon(x,P,PSL):
    a,b,c,d,z=x
    if PSL:
        f=a if a else c
        if f>(P-1)//2: return ((-a)%P,(-b)%P,(-c)%P,(-d)%P,z)
    return x
def inv(x,P,n):
    a,b,c,d,z=x
    return (d%P,(-b)%P,(-c)%P,a%P,(-z)%n)
if __name__=='__main__':
    fn=sys.argv[1]; P=int(sys.argv[2]); n=int(sys.argv[3]); PSL=sys.argv[4]=='psl' if len(sys.argv)>4 else False
    d,nn,gens=parse(fn)
    # find alpha of projective order 3 as in choose_alpha: g=[[0,-1],[1,t]], t tried P-1 first
    def pw(x,k):
        y=(1,0,0,1,0)
        for _ in range(k): y=mul(y,x,P,n); y=canon(y,P,PSL)
        return y
    AG=None
    for tt in range(P):
        t = P-1 if tt==0 else tt-1
        if tt>0 and t==P-1: continue
        g=canon((0,P-1,1,t,0),P,PSL)
        y=(1,0,0,1,0); pm=False
        for i in range(1,4):
            y=canon(mul(y,g,P,n),P,PSL)
            if (y[0]==1 and y[3]==1 and y[1]==0 and y[2]==0) or (y[0]==P-1 and y[3]==P-1 and y[1]==0 and y[2]==0):
                pm = (i==3); break
        if pm: AG=g; break
    print('AG',AG)
    # AR: r of order 3 mod n with fewest fixed points
    import math
    AR=None; best=None
    if n>1:
        for r in range(2,n):
            if math.gcd(r,n)!=1 or pow(r,3,n)!=1: continue
            fx=math.gcd(r-1,n)
            if best is None or fx<best: best=fx; AR=r
    else: AR=1
    print('AR',AR)
    AGI=inv(AG,P,n)
    def alpha(x):
        y=mul(mul(AG,x,P,n),AGI,P,n); y=canon(y,P,PSL)
        return (y[0],y[1],y[2],y[3],(AR*x[4])%n)
    for i,gx in enumerate(gens):
        o=[gx]; cur=gx
        for _ in range(3):
            cur=canon(alpha(cur),P,PSL); o.append(cur)
        orb=o[:3]
        print(i,gx, 'orbit-size-3-closed' if o[3]==canon(gx,P,PSL) else 'not-order3')
