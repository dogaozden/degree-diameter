import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mkgroup import table, check, write
# (m,k,t,r): metacyclic (Z_m x|_r Z_k) x Z_t ; r chosen with r^k = 1 mod m, r != 1 (nonabelian)
specs = [(43,7,1,None),(31,10,1,None),(41,8,1,None),(37,9,1,None),(13,24,1,None),(61,5,1,None),(103,3,1,None),(79,4,1,None),(163,2,1,None),(99,3,1,None)]
out = []
for m,k,t,r in specs:
    if r is None:
        cands = [x for x in range(2,m) if pow(x,k,m)==1]
        # pick the candidate of largest multiplicative order (faithful as far as possible)
        def order(x):
            o=1; y=x
            while y!=1: y=y*x%m; o+=1
            return o
        cands.sort(key=order, reverse=True)
        r = cands[0]
    N, mul = table(m,k,r,t); check(N,mul)
    name = f"g{N}_Z{m}x{r}Z{k}xZ{t}"
    path = f"tables/{name}.tab"
    write(path, 1, name, N, mul)
    out.append((N, path, m, k, r))
    print(N, path, "r=",r, "order_r=", next(o for o in range(1,m+1) if pow(r,o,m)==1), flush=True)
