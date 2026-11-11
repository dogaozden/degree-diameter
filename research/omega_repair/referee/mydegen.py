# Independent enumeration for Lemma 4.3 (q=7): partial linear spaces on {0=t,1..5}, blocks of size>=3 meeting pairwise in <=1 point.
from itertools import combinations
from fractions import Fraction
q=7; m2=140
PO=q**3-q; T3=(q+1)**2
pts=range(6)
blocks=[frozenset(c) for k in (3,4,5,6) for c in combinations(pts,k)]
fams=[]
def rec(i,cur):
    if i==len(blocks): fams.append(list(cur)); return
    rec(i+1,cur)
    b=blocks[i]
    if all(len(b&c)<=1 for c in cur):
        cur.append(b); rec(i+1,cur); cur.pop()
rec(0,[])
print("partial linear spaces:",len(fams))
Y=[1,2,3,4,5]
res={}
worst=[]
for fam in fams:
    def blk(s):
        for b in fam:
            if s<=b: return b
        return None
    def aligned(i,j):
        b=blk(frozenset((0,i,j))); return b is not None
    # union bound
    if any(0 not in b and len(b)==5 for b in fam):
        U=5*q**4-4*PO
    else:
        U=5*q**4
        for i,j in combinations(Y,2):
            if aligned(i,j): continue
            U-=PO   # overlap >= PO (rich-line value X>=PO; coefficient handled below)
        for tr in combinations(Y,3):
            if any(aligned(a,b) for a,b in combinations(tr,2)): continue
            b=blk(frozenset(tr))
            if b is not None:
                assert 0 not in b
                U+=PO   # rich triple overlap = X; pairs on line also X. we lower-bounded pairs by PO; need net coefficient >=0 check
            else:
                U+=T3
        # check net X coefficient on each rich line: pairs - triples >= 0
        for b in fam:
            if 0 in b: continue
            m=len(b); assert m*(m-1)//2 - m*(m-1)*(m-2)//6 >= 0
    far=q**5-U-m2*q*q
    # forced perpendicular pairs: any pair inside a block
    fp=sum(1 for a,c in combinations(pts,2) if blk(frozenset((a,c))) is not None)
    # type key: sizes of t-blocks (classes of y's), and sizes of rich lines
    tcls=sorted([len(b)-1 for b in fam if 0 in b])
    ncl=5-sum(tcls); cls=tuple(sorted(tcls+[1]*ncl))
    rich=tuple(sorted(len(b) for b in fam if 0 not in b))
    key=(cls,rich)
    r=res.setdefault(key,[10**9,10**9,0])
    r[0]=min(r[0],far); r[1]=min(r[1],fp); r[2]+=1
    if far<=0 and fp<6: worst.append((fam,far,fp))
print("types:",len(res))
for k,v in sorted(res.items(),key=lambda kv:kv[1][0]):
    print(k,"far>=",v[0],"fp>=",v[1],"instances",v[2])
print("instances with no forced far vertex and <6 forced perp pairs:",len(worst))
print("min fp over non-forced:",min(v[1] for v in res.values() if v[0]<=0))
print("min fp over all instances with far<=0:", min((fp for fam in fams for fp in [0]) ,default=None))
