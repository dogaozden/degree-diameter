import itertools
def qo(kind,q):
    if kind in ('sl','pgl'): return q*(q*q-1)
    if kind=='psl': return q*(q*q-1)//(1 if q%2==0 else 2)
    if kind=='agl1': return q*(q-1)
basic=[]
for q in [2,3,4,5,7,8,9,11,13]: basic.append(('sl',q))
for q in [3,5,7,9,11,13]: basic.append(('psl',q))
for q in [2,3,4,5,7,9,11,13]: basic.append(('pgl',q))
for q in [3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47]: basic.append(('agl1',q))
def isprime(n): return n>1 and all(n%p for p in range(2,int(n**0.5)+1))
def ok_n(n):
    if n==1: return True
    m=n; ps=[]
    p=2
    while p*p<=m:
        while m%p==0: ps.append(p); m//=p
        p+=1
    if m>1: ps.append(m)
    # all primes 1 mod 3 -> clean; or allow a single factor 2 (fix x2) and 1-mod-3 primes
    bad=[p for p in ps if p%3!=1]
    return len(bad)==0 or (set(bad)=={2} and bad.count(2)==1)
out=[]
for k in (2,3):
    for combo in itertools.combinations_with_replacement(basic,k):
        o=1
        for kind,q in combo: o*=qo(kind,q)
        if o>2100: continue
        # need Q nonabelian-ish: skip if any agl1 q with q<=3 only etc: keep all
        for n in range(1,2101):
            N=o*n
            if 2001<=N<=2100 and ok_n(n):
                name=' '.join(f'{kind} {q}' for kind,q in combo)
                out.append((N,n,name))
out.sort()
for N,n,name in out: print(N,n,name)
