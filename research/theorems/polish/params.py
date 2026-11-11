# smallest c (with -c a non-square) and (c0,c1) with G(a,b)=(c0 a+c1 b)(a^2+c b^2)-b^3 != 0 on F^2\{0}; primes only
for q in [3,5,7,11,13]:
    sq={x*x%q for x in range(q)}
    for c in range(1,q):
        if (-c)%q in sq: continue
        found=None
        for c0 in range(1,q):
            for c1 in range(q):
                if all(((c0*a+c1*b)*(a*a+c*b*b)-b**3)%q for a in range(q) for b in range(q) if (a,b)!=(0,0)):
                    found=(c0,c1);break
            if found:break
        print(q,'c',c,'(c0,c1)',found); break
