import sys
from collections import Counter
f=sys.argv[1]; out=sys.argv[2]; want=set(map(int,sys.argv[3].split(','))) if len(sys.argv)>3 else None
L=open(f).read().split('\n')
m=int(L[0]); mul=[list(map(int,L[1+i].split())) for i in range(m)]
def order(g):
    k=1; x=g
    while x!=0: x=mul[x][g]; k+=1
    return k
ords=[order(g) for g in range(m)]
print('histogram', sorted(Counter(ords).items()))
if want:
    pool=[g for g in range(m) if g!=0 and ords[g] in want]
    open(out,'w').write(' '.join(map(str,pool))+'\n')
    print('pool size', len(pool))
