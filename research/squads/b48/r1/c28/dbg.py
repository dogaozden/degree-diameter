import random
m,k,r=55,20,2
N=m*k
PW=[pow(r,j,m) for j in range(k)]
def mul(g,h):
    a,j=g%m,g//m; c,l=h%m,h//m
    return (a+PW[j]*c)%m + m*((j+l)%k)
S=[]
random.seed(3)
odd=[g for g in range(N) if (g//m)%2==1]
def inv(g):
    a,j=g%m,g//m; jj=(k-j)%k
    return ((-PW[jj]*a)%m)+m*jj
# check group law and inverse
for _ in range(2000):
    x,y,z=random.randrange(N),random.randrange(N),random.randrange(N)
    assert mul(mul(x,y),z)==mul(x,mul(y,z))
    assert mul(x,inv(x))==0
print("group ok")
for trial in range(3):
    x=random.choice(odd); y=random.choice(odd)
    S=[x,inv(x),y,inv(y)]
    if len(set(S))<4: continue
    seen={0:0}; front=[0]
    for d in range(1,9):
        nf=[]
        for g in front:
            for s in S:
                h=mul(g,s)
                if h not in seen: seen[h]=d; nf.append(h)
        front=nf
        print(d,len(nf),end='; ')
    print("\nball8 covered", len(seen), "of", N, "S",S)
