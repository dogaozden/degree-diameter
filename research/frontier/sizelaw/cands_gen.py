"""All haar_gen3 groups (sl/psl/pgl/agl1 q, products of two with small first factor) x Z_n with order in [lo, hi].
Prints 'spec|N' lines (spec = haar_gen3 GROUP... n)."""
import sys
from sympy import factorint
lo,hi=int(sys.argv[1]),int(sys.argv[2])
pp=lambda q: len(factorint(q))==1
qs=[q for q in range(3,1200) if pp(q)]
base=[]
for q in qs:
    o=q*(q*q-1)
    if o<=hi: base.append(('sl %d'%q,o)); base.append(('pgl %d'%q,o))
    if q%2 and o//2<=hi: base.append(('psl %d'%q,o//2))
    if q*(q-1)<=hi and q>3: base.append(('agl1 %d'%q,q*(q-1)))
small=[(s,o) for s,o in base if o<=2000 and not s.startswith('agl1')]
prods=[]
for i,(s1,o1) in enumerate(small):
    for s2,o2 in base:
        if o1*o2<=hi and o2>=o1 and not s2.startswith('agl1'): prods.append(('prod %s %s'%(s1,s2),o1*o2))
out=set()
for s,o in base+prods:
    for n in range(1,400):
        N=o*n
        if N>hi: break
        if N>=lo: out.add((N,'%s %d'%(s,n)))
for N,s in sorted(out): print('%s|%d'%(s,N))
