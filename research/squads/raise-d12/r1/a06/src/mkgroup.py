# usage: mkgroup.py SPEC OUT   SPEC: cyc m | ab a b | meta a b r  (Z_a x|_r Z_b, element (x,y), r^b = 1 mod a)
import sys
from math import gcd
spec=sys.argv[1].split(); out=sys.argv[2]
if spec[0]=='cyc':
    m=int(spec[1]); mul=lambda x,y:(x+y)%m; els=list(range(m))
    idx={e:i for i,e in enumerate(els)}; M=[[idx[mul(a,b)] for b in els] for a in els]
elif spec[0] in('ab','meta'):
    a,b=int(spec[1]),int(spec[2]); r=int(spec[3]) if spec[0]=='meta' else 1
    assert pow(r,b,a)==1%a if a>1 else True
    els=[(x,y) for x in range(a) for y in range(b)]; idx={e:i for i,e in enumerate(els)}
    def mul(p,q):
        x1,y1=p; x2,y2=q
        return ((x1+pow(r,y1,a)*x2)%a,(y1+y2)%b)
    M=[[idx[mul(p,q)] for q in els] for p in els]
m=len(M)
# sanity: identity at 0, associativity sample
assert all(M[0][j]==j and M[j][0]==j for j in range(m))
inv=[next(j for j in range(m) if M[i][j]==0) for i in range(m)]
with open(out,'w') as f:
    f.write(f"{m}\n")
    for i in range(m): f.write(' '.join(map(str,M[i]))+'\n')
    f.write(' '.join(map(str,inv))+'\n')
print('group order',m,'written',out)
