# Convert the note's q = 3 annealed twist file (normal form: lam_c as point and line permutations of the H(3) written
# by its hexq6.c) to omg's labelling format (P_c = identity, L_c = lam_c), after checking every lam_c is a collineation.
# usage: convert_theirs.py their_hex.txt their_twists.bin out_hex.txt out_lab.bin
import sys, numpy as np
f=open(sys.argv[1]).read().split('\n')
q,n,nl=map(int,f[0].split())
lines=[list(map(int,f[1+i].split())) for i in range(nl)]
open(sys.argv[3],'w').write("%d %d\n"%(q,n)+"\n".join(" ".join(map(str,L)) for L in lines)+"\n")
d=np.fromfile(sys.argv[2],dtype=np.int32); C,N=int(d[0]),int(d[1]); body=d[2:].reshape(C,2,N)
key={tuple(sorted(L)):i for i,L in enumerate(lines)}
ok=sum(all(key.get(tuple(sorted(int(body[c,0][p]) for p in L)))==int(body[c,1][i]) for i,L in enumerate(lines)) for c in range(C))
print("twist file %s: C=%d n=%d; lam_c maps every line to the stated line (a collineation): %d/%d"%(sys.argv[2],C,N,ok,C))
with open(sys.argv[4],'wb') as g:
    np.array([C,N],dtype=np.int32).tofile(g)
    for c in range(C): np.arange(N,dtype=np.int32).tofile(g); body[c,1].astype(np.int32).tofile(g)
