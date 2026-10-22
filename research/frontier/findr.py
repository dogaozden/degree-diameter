import sys, math
def order(r,m):
    x=r%m; o=1
    while x!=1:
        x=x*r%m; o+=1
        if o>m: return None
    return o
def rs(m,k):
    return [r for r in range(2,m) if math.gcd(r,m)==1 and order(r,m)==k]
if __name__=="__main__":
    m,k=int(sys.argv[1]),int(sys.argv[2]); L=rs(m,k); print(len(L), L[:10])
