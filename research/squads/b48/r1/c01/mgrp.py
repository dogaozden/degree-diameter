class Meta:
    """Z_m x|_r Z_k, element index a + m*j, (a,j)(b,l) = (a + r^j b, j+l)"""
    def __init__(s,m,k,r):
        s.m,s.k,s.r=m,k,r; s.N=m*k
        assert pow(r,k,m)==1
        s.rp=[pow(r,j,m) for j in range(k)]
    def mul(s,x,y):
        a,j=x%s.m,x//s.m; b,l=y%s.m,y//s.m
        return (a+s.rp[j]*b)%s.m + s.m*((j+l)%s.k)
    def inv(s,x):
        a,j=x%s.m,x//s.m
        ri=pow(s.r,(-j)%s.k,s.m)
        return ((-ri*a)%s.m) + s.m*((-j)%s.k)
    def coord(s,x): return (x%s.m, x//s.m)
