# f03: random Z_n voltage lifts of a base: uncovered (endpoint,voltage) pairs per source, vs the Poisson model
import numpy as np, sys, time
from walks import base_gp, base_k44, base_k33, base_cube, walks, distinct_counts
which=sys.argv[1]; D=int(sys.argv[2]); ns=[int(x) for x in sys.argv[3].split(',')]; trials=int(sys.argv[4])
V,edges={'gp':lambda:base_gp(10,3),'k44':base_k44,'k33':base_k33,'cube':base_cube}[which]()
E=len(edges)
out=walks(V,edges,0,D)
# per-source walk data (vertex-transitive bases: only check sources 0..V-1 if asked)
src_out=[out]+[walks(V,edges,s,D) for s in range(1,V)] if which=='gp' and len(sys.argv)>5 else None
_,per=distinct_counts(V,out,D)
print(which,"D",D,"V",V,"E",E,"W_v(distinct, len<=D) min/max/total",per.min(),per.max(),per.sum(),flush=True)
# flatten per source: endpoint array and X (int8) limited to len<=D
def flat(o):
    ends=np.concatenate([c for c,_ in o]); X=np.concatenate([x for _,x in o]); return ends.astype(np.int64),X.astype(np.int64)
sources=[flat(out)]
if src_out is not None:
    sources=[flat(o) for o in src_out]
else:
    # sources are equivalent only for vertex-transitive bases; sample a few sources from different orbits
    for s in range(1,V):
        pass
rng=np.random.default_rng(7)
for n in ns:
    mu1=sum(n*(1-1/n)**int(p) for p in per)
    cnt_ok=0; unc=[]; t=time.time()
    for tr in range(trials):
        a=rng.integers(0,n,size=E,dtype=np.int64)
        tot_unc=0; ok=True
        for (ends,X) in sources[:1] if src_out is None else sources:
            volt=(X@a)%n
            u=len(np.unique(ends*n+volt))
            un=V*n-u
            tot_unc+=un
            if un: ok=False
        unc.append(tot_unc/len(sources[:1] if src_out is None else sources)); cnt_ok+=ok
    print(f"n={n} N={V*n} model_mu_per_source={mu1:.3f} empirical_mean_uncovered_per_source={np.mean(unc):.3f} P(all covered)={cnt_ok/trials:.4f} trials={trials} time={time.time()-t:.1f}",flush=True)
