"""build_q.py: enumerate a subgroup Q of GL(2,p) from generator matrices and write the cay_mg group file.
 python3 build_q.py OUT p lmax a b c d  a b c d ..."""
import sys,struct
def mm(X,Y,p): return ((X[0]*Y[0]+X[1]*Y[2])%p,(X[0]*Y[1]+X[1]*Y[3])%p,(X[2]*Y[0]+X[3]*Y[2])%p,(X[2]*Y[1]+X[3]*Y[3])%p)
def enum_group(p,gens,lmax):
    I=(1,0,0,1); els=[I]; seen={I}; i=0
    while i<len(els):
        x=els[i]; i+=1
        for g in gens:
            y=mm(g,x,p)
            if y not in seen:
                seen.add(y); els.append(y)
                if len(els)>lmax: return None
    return els
def write(out,p,els):
    with open(out,'wb') as f:
        f.write(struct.pack('ii',p,len(els)))
        for e in els: f.write(struct.pack('iiii',*e))
if __name__=='__main__':
    out=sys.argv[1];p=int(sys.argv[2]);lmax=int(sys.argv[3]); v=list(map(int,sys.argv[4:]))
    gens=[tuple(x%p for x in v[i:i+4]) for i in range(0,len(v),4)]
    els=enum_group(p,gens,lmax); print(len(els) if els else None)
    if els: write(out,p,els)
