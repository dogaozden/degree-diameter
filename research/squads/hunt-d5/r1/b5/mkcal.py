import itertools, struct, array, sys
sys.path.insert(0,'.')
from mktab import direct, write
S4=list(itertools.permutations(range(4)))  # identity first
idx={p:i for i,p in enumerate(S4)}
N=len(S4); T=[0]*(N*N)
for a,p in enumerate(S4):
    for b,q in enumerate(S4):
        T[a*N+b]=idx[tuple(p[q[i]] for i in range(4))]
def cyc(n): return n,[ (i+j)%n for i in range(n) for j in range(n)]
write('s4z24.bin', direct((N,T),cyc(24)))
write('s4z27.bin', direct((N,T),cyc(27)))
print('ok')
