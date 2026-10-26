# enumerate 2x2 matrices mod p, report order and whether the char poly is irreducible (Singer type)
import itertools, sys
def mul(A,B,p):
    return ((A[0]*B[0]+A[1]*B[2])%p, (A[0]*B[1]+A[1]*B[3])%p, (A[2]*B[0]+A[3]*B[2])%p, (A[2]*B[1]+A[3]*B[3])%p)
def order(M,p,maxo=200):
    I=(1,0,0,1); P=M
    for k in range(1,maxo+1):
        if P==I: return k
        P=mul(P,M,p)
    return None
def irreducible(M,p):
    a,b,c,d=M; t=(a+d)%p; det=(a*d-b*c)%p
    # x^2 - t x + det irreducible iff no root in F_p
    return all((x*x-t*x+det)%p!=0 for x in range(p))
def run(p, want_orders):
    out={}
    for M in itertools.product(range(p),repeat=4):
        a,b,c,d=M
        if (a*d-b*c)%p==0: continue
        o=order(M,p)
        if o in want_orders:
            key=(o, irreducible(M,p))
            out.setdefault(key,[]).append(M)
    return out
if __name__=="__main__":
    p=int(sys.argv[1]); orders=[int(x) for x in sys.argv[2].split(',')]
    res=run(p,set(orders))
    for key in sorted(res):
        print("order",key[0],"irreducible" if key[1] else "reducible/split", "count",len(res[key]),"example",res[key][0])
