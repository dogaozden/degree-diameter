import math
from fm import W, mu, lnC_rand, lnC_orb
# (label, delta, D, |G|, form, m, f) ; |G| = record vertices / 2
recs = [
 ("(4,13) meta Z4903x|230 Z19 (rand)",4,13,93157,"rand",None,None),
 ("(5,13) prod Frobenius (rand)",5,13,1762649,"rand",None,None),
 ("(6,13) PSL(2,83)xZ73 (orb 3 2 0)",6,13,20867196,"orb",2,0),
 ("(7,13) SL(2,229)xZ13 (orb 3 2 1)",7,13,156113880,"orb",2,1),
 ("(8,13) SL(2,499)xZ7 (orb 3 2 2)",8,13,869757000,"orb",2,2),
 ("(9,13) SL(2,661)xZ13 (orb 3 3 0)",9,13,3754453560,"orb",3,0),
 ("(6,14) SL(2,97)xZ103 (orb 3 2 0)",6,14,93995328,"orb",2,0),
 ("(7,14) SL(2,163)xZ193 (orb 3 2 1)",7,14,835802712,"orb",2,1),
]
print(f"{'cell':36s} {'N':>12s} {'mu':>8s} {'lnC_form':>9s} {'lnC-mu':>8s}   {'lnC_rand':>8s} {'lnC_orb(same d)':>15s}")
for lab,d,D,N,form,m,f in recs:
    mu_ = mu(N,d,D)
    if form=="rand":
        lc = lnC_rand(N,d); lo=float('nan')
    else:
        lc = lnC_orb(N,d,f,m, fix=35)
        lo = lnC_rand(N,d)
    print(f"{lab:36s} {N:12d} {mu_:8.2f} {lc:9.2f} {lc-mu_:8.2f}   {lnC_rand(N,d):8.2f} {lo if form=='orb' else float('nan'):15.2f}")
print()
# Delta=4 scan at D=13: budget of both forms vs N (Poisson, P0=e^-mu, orbit events mu/3)
print("Delta=4, D=13: ln(#cand) per form vs |G|, and mu (size law)")
for N in [1e5,3e5,1e6,3e6,1e7,3e7]:
    N=int(N)
    print(f"N={N:>9d} mu={mu(N,4,13):7.2f}  rand lnC={lnC_rand(N,4):6.2f}  orb(3 1 1) lnC={lnC_orb(N,4,1,1):6.2f}  orb events budget 3*lnC_orb={3*lnC_orb(N,4,1,1):6.2f}")
print()
print("Delta=5, D=13 (rand, d=5): N, mu, rand lnC")
for N in [1e6,1e7,1e8]:
    print(f"N={int(N):>10d} mu={mu(int(N),5,13):8.2f} lnC={lnC_rand(int(N),5):6.2f}")
