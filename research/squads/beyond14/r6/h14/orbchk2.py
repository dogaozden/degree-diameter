import sys
from orbchk import parse, mul, canon, inv
import math
fn=sys.argv[1]; P=int(sys.argv[2]); n=int(sys.argv[3]); PSL=len(sys.argv)>4 and sys.argv[4]=='psl'
d,nn,gens=parse(fn)
AG=(0,P-1,1,P-1,0); AR=28 if n==271 else None
AGI=inv(AG,P,n)
def alpha(x):
    y=mul(mul(AG,x,P,n),AGI,P,n); y=canon(y,P,PSL)
    return (y[0],y[1],y[2],y[3],(AR*x[4])%n)
S=[canon(g,P,PSL) for g in gens]
for i,g in enumerate(S):
    a=canon(alpha(g),P,PSL); a2=canon(alpha(a),P,PSL)
    ia=[j for j,h in enumerate(S) if h==a]; 
    fixed = (a==g)
    print(i, 'fixed' if fixed else ('alpha in S at %s'%ia if ia else 'alpha not in S'))
