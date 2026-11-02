import math, sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise_d8b/r3/e13")
from math import gcd
import importlib.util
spec = importlib.util.spec_from_file_location("ha", "/home/user/degree-diameter/research/squads/raise_d8b/r3/e13/holes_analyze.py")
# constants copied from the log lines (lambda = W/N)
LAM = {"d01_a.sol.best": 13.366, "d02_start.sol.best": 13.318, "d05_a.sol.best": 13.428, "d06_d06.sol.best": 13.458,
       "d07_a.sol.best": 14.067, "d09_a.sol.best": 14.040, "d10_a.sol.best": 14.001, "d11_a.sol.best.orb": 14.611,
       "d12_a.sol.best.orb": 14.564, "d13_a.sol.best.orb": 14.429}
ST = {"d02_start.sol.best": ("psl",89,61,5,9,9), "d05_a.sol.best": ("sl",31,1091,5,12,93),
      "d09_a.sol.best": ("psl",89,131,5,9,53), "d10_a.sol.best": ("psl",59,451,5,25,16),
      "d11_a.sol.best.orb": ("sl",79,131,5,29,53), "d12_a.sol.best.orb": ("psl",61,571,5,17,106),
      "d13_a.sol.best.orb": ("psl",109,101,5,10,36)}
for name,(fam,p,n,k,t,AR) in ST.items():
    psl = fam=="psl"
    AG=(0,p-1,1,t); AGI=(t,1,p-1,0)
    def mm(A,B):
        return ((A[0]*B[0]+A[1]*B[2])%p,(A[0]*B[1]+A[1]*B[3])%p,(A[2]*B[0]+A[3]*B[2])%p,(A[2]*B[1]+A[3]*B[3])%p)
    def nm(M):
        if not psl: return M
        neg=tuple((-x)%p for x in M); return min(M,neg)
    # count matrices x in SL(2,p) with alpha(x)=x (projectively for PSL), z-part: AR z = z mod n
    F = 0
    for a in range(p):
        for b in range(p):
            for c in range(p):
                # solve d from det=1 when a!=0; else use b*c = -1
                if a:
                    d = (1 + b*c) * pow(a, p-2, p) % p
                    cands = [(a,b,c,d)]
                else:
                    if (b*c) % p != p-1: continue
                    cands = [(0,b,c,d) for d in range(p)]
                for M in cands:
                    if (M[0]*M[3]-M[1]*M[2]) % p != 1: continue
                    if nm(mm(mm(AG,M),AGI)) == nm(M): F += 1
    if psl: F //= 1  # projective count: each PSL element counted twice (x and -x)
    # PSL elements: SL count / 2 ; SL elements: count as is
    Fe = F // 2 if psl else F
    zf = gcd(AR-1, n)   # number of z in Z_n with AR z = z
    Ftot = Fe * zf
    lam = LAM[name]
    exp_fixed = (Ftot - 1) * math.exp(-lam / k)
    print("%-22s %s p=%d n=%d |fixed elements (non-identity)|=%d  gcd(AR-1,n)=%d  expected fixed holes ~ %.2f" % (name, fam, p, n, Ftot-1, zf, exp_fixed))
