import sys
def order(r,m):
    x=r%m; o=1
    while x!=1: x=x*r%m; o+=1
    return o
for m,k in [(29,28),(139,6),(43,21),(113,8),(61,15),(31,30),(157,6),(89,11),(109,9),(71,14)]:
    rs=[r for r in range(2,m) if order(r,m)==k]
    print(m,k,m*k,rs[0] if rs else None)
