import itertools, random, os
random.seed(7)
D='/home/user/degree-diameter/research/squads/f65r1/c5'
GD=D+'/grp'; os.makedirs(GD,exist_ok=True)

def table_from(elems, prod, ident):
    elems=[ident]+[e for e in elems if e!=ident]
    idx={e:i for i,e in enumerate(elems)}
    return [[idx[prod(a,b)] for b in elems] for a in elems]

def cyc(k): return [[(i+j)%k for j in range(k)] for i in range(k)]

def meta(m,k,r):
    assert pow(r,k,m)==1%m, (m,k,r)
    elems=[(a,b) for a in range(m) for b in range(k)]
    def prod(x,y):
        a1,b1=x; a2,b2=y
        return ((a1+pow(r,b1,m)*a2)%m,(b1+b2)%k)
    return table_from(elems,prod,(0,0))

def compose(p,q): return tuple(p[q[i]] for i in range(len(q)))
def parity(p):
    s=0
    for i in range(len(p)):
        for j in range(i+1,len(p)):
            if p[i]>p[j]: s+=1
    return s%2
def symgrp(nn, alt):
    el=[p for p in itertools.permutations(range(nn)) if (parity(p)==0)==alt or not alt]
    return table_from(el,compose,tuple(range(nn)))

def sl23():
    el=[m for m in itertools.product(range(3),repeat=4) if (m[0]*m[3]-m[1]*m[2])%3==1]
    def prod(x,y):
        a,b,c,d=x; e,f,g,h=y
        return ((a*e+b*g)%3,(a*f+b*h)%3,(c*e+d*g)%3,(c*f+d*h)%3)
    return table_from(el,prod,(1,0,0,1))

def dprod(T1,T2):
    n1,n2=len(T1),len(T2); n=n1*n2
    mul=[[0]*n for _ in range(n)]
    for i in range(n):
        a,b=divmod(i,n2); row=mul[i]
        for j in range(n):
            c,d=divmod(j,n2)
            row[j]=T1[a][c]*n2+T2[b][d]
    return mul

def invs(T):
    n=len(T); inv=[0]*n
    for i in range(n):
        for j in range(n):
            if T[i][j]==0: inv[i]=j
    return inv
def orders(T):
    n=len(T); o=[0]*n
    for i in range(n):
        k=1; x=i
        while x!=0: x=T[x][i]; k+=1
        o[i]=k
    return o
def closure(T,gens):
    seen={0}; st=[0]
    while st:
        x=st.pop()
        for g in gens:
            y=T[x][g]
            if y not in seen: seen.add(y); st.append(y)
    return len(seen)

def inv_auts(T):
    n=len(T); o=orders(T)
    gens=None
    for _ in range(200000):
        g1=random.randrange(1,n); g2=random.randrange(1,n)
        if closure(T,[g1,g2])==n: gens=(g1,g2); break
    assert gens, "no 2-generation"
    g1,g2=gens
    res=[]
    C1=[h for h in range(n) if o[h]==o[g1]]; C2=[h for h in range(n) if o[h]==o[g2]]
    for h1 in C1:
        for h2 in C2:
            phi=[-1]*n; phi[0]=0; q=[0]; qi=0; ok=True
            while qi<len(q) and ok:
                x=q[qi]; qi+=1
                for gi,hi in ((g1,h1),(g2,h2)):
                    y=T[x][gi]; val=T[phi[x]][hi]
                    if phi[y]==-1: phi[y]=val; q.append(y)
                    elif phi[y]!=val: ok=False; break
            if not ok or len(set(phi))!=n: continue
            if any(phi[phi[x]]!=x for x in range(n)): continue
            res.append(phi)
    return res

def write_group(name,T,auts,nsample=4):
    n=len(T)
    with open(f'{GD}/{name}.grp','w') as f:
        f.write(f'{n}\n')
        for row in T: f.write(' '.join(map(str,row))+'\n')
    if auts:
        samp=[list(range(n))]
        others=[a for a in auts if a!=list(range(n))]
        random.shuffle(others)
        samp+=others[:nsample]
    else:
        samp=[list(range(n))]
    for j,a in enumerate(samp):
        with open(f'{GD}/{name}.aut{j}','w') as f: f.write(' '.join(map(str,a))+'\n')
    print(name,'order',n,'involutive auts found',len(auts),'written',len(samp),flush=True)

if __name__=='__main__':
    A5=symgrp(5,True); S4=symgrp(4,False); SL=sl23(); Z3=cyc(3); Z8=cyc(8)
    tabs={}
    def fac_auts(T): return inv_auts(T)
    # product groups: aut = product of factor involutive auts
    def prod_auts(T1,a1,T2,a2):
        n1,n2=len(T1),len(T2); out=[]
        for p1 in a1:
            for p2 in a2:
                out.append([p1[i]*n2+p2[j] for i in range(n1) for j in range(n2)])
        return out
    A5a=fac_auts(A5); Z3a=fac_auts(Z3); SLa=fac_auts(SL); S4a=fac_auts(S4); Z8a=fac_auts(Z8)
    print('factor auts A5',len(A5a),'Z3',len(Z3a),'SL23',len(SLa),'S4',len(S4a),'Z8',len(Z8a),flush=True)
    write_group('A5xZ3', dprod(A5,Z3), prod_auts(A5,A5a,Z3,Z3a), 6)
    write_group('SL23xZ8', dprod(SL,Z8), prod_auts(SL,SLa,Z8,Z8a), 6)
    write_group('S4xZ8', dprod(S4,Z8), prod_auts(S4,S4a,Z8,Z8a), 6)
    specs={'Z31_r26':(31,6,26),'Z31_r5':(31,6,5),'Z31_rm1':(31,6,30),'Z43_rm1':(43,4,42),
           'Z13_rm1':(13,14,12),'Z23_rm1':(23,8,22),'Z11_rm1':(11,16,10),'Z5_r2':(5,36,2)}
    for name,(m,k,r) in specs.items():
        T=meta(m,k,r)
        write_group(name,T,inv_auts(T),4)
