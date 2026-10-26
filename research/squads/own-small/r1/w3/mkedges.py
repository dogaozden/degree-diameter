import numpy as np, sys
# usage: mkedges.py S0 S1 S2 S3 OUT  (Haar graph H(A7,S): (0,x)~(1,s x); vertex (0,x)=x, (1,x)=N+x)
N=2520
mul=np.fromfile('mul.bin',dtype='<u2').reshape(N,N)
S=[int(v) for v in sys.argv[1:5]]; out=sys.argv[5]
with open(out,'w') as f:
    f.write(f"{2*N}\n")
    for s in S:
        for x in range(N):
            f.write(f"{x} {N+int(mul[s][x])}\n")
print("wrote",out)
