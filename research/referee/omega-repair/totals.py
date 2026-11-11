import sys
from myroutes import wiring,routes,summary
q=int(sys.argv[1]); alpha=int(sys.argv[2]); N=(q**6-1)//(q-1)
for na in range(alpha+1):
    pattern='a'*na+'b'*(alpha-na)
    C,meets=wiring(pattern)
    tot=0; pos=0; npairs=0
    for X in C:
        for cp in range(5*alpha):
            if cp in C[X]: continue
            npairs+=1
            b=routes(pattern,X,cp); b.pop((),None)
            m,_=summary(b)
            bound=q**5-m[4]*q**4-m[2]*q*q-m.get(0,0)
            if bound>0: pos+=1; tot+=N*bound
    print("q=%d %-9s %d of %d pairs positive; far (hub, vertex) pairs >= %.4g"%(q,pattern,pos,npairs,tot),flush=True)
