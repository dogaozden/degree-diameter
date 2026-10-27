import sys,time
from myroutes import wiring,routes,summary
q=int(sys.argv[1]); alpha=int(sys.argv[2])
worst=None
for na in range(alpha+1):
    pattern='a'*na+'b'*(alpha-na)
    C,meets=wiring(pattern)
    best=None
    for X in C:
        for cp in range(5*alpha):
            if cp in C[X]: continue
            b=routes(pattern,X,cp)
            ident=b.pop((),None)       # identity word: its ball lies in B(t,4), misses opp(t)
            m,_=summary(b)
            tw4=m[4]; m0=m.get(0,0)
            bound=q**5-tw4*q**4-m[2]*q*q-m0
            if best is None or bound>best[0]: best=(bound,X,cp,tw4,m[2],m0)
    print("q=%d %-10s best pair X=%s c'=%2d twisted r4=%d m2=%d m0=%d -> far per hub >= %d"%((q,pattern)+best[1:3]+best[3:]+(best[0],)),flush=True)
    if worst is None or best[0]<worst[0]: worst=(best[0],pattern,best[4])
print("worst pattern %s: m2=%d bound %d"%(worst[1],worst[2],worst[0]))
