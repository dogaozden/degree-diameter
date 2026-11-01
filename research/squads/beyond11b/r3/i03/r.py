import sys
def order(r,p):
    o=1; x=r
    while x!=1: x=x*r%p; o+=1
    return o
def rr(p,k):
    for x in range(2,p):
        r=pow(x,(p-1)//k,p)
        if order(r,p)==k: return r
    return None
if __name__=="__main__":
    for a in sys.argv[1:]:
        p,k=map(int,a.split(':')); print(a, rr(p,k))
