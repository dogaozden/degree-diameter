# e14 fit: per-side measured median (cost/2) vs odd-D hole-model terms, (d,D)=(11,9), ORBIT "3 3 2"
import math, re, statistics, numpy as np
W = 111111111; h = 4
groups = [("sl_199_1","sl",199,1),("psl_251_1","psl",251,1),("psl_131_7","psl",131,7),("psl_107_13","psl",107,13),
 ("sl_29_331","sl",29,331),("sl_43_103","sl",43,103),("psl_53_109","psl",53,109),("sl_37_157","sl",37,157),
 ("sl_29_307","sl",29,307),("psl_59_73","psl",59,73),("sl_41_109","sl",41,109),("sl_37_151","sl",37,151),
 ("psl_43_193","psl",43,193),("psl_41_223","psl",41,223),("sl_43_97","sl",43,97),("psl_37_307","psl",37,307),
 ("sl_29_349","sl",29,349),("sl_107_7","sl",107,7),("sl_43_109","sl",43,109),("psl_97_19","psl",97,19),
 ("sl_29_367","sl",29,367),("psl_37_349","psl",37,349)]
rows=[]
for name,fam,p,n in groups:
    costs=[int(x) for x in re.findall(r"cost (\d+)", open(f"ro_{name}.err").read())]
    N=(p*(p*p-1) if fam=="sl" else p*(p*p-1)//2)*n
    lam=W/N; mu=N*math.exp(-lam)
    I = 1 if fam=="sl" else p*(p+(1 if p%4==1 else -1))//2
    C = 2*n if fam=="sl" else n
    F = (p-(1 if p%3==1 else -1))*(1 if fam=="sl" else 0.5)
    rows.append(dict(name=name,N=N,lam=lam,mu=mu,I=I,C=C,F=F,tI=I*math.exp(-lam/2),tC=C*math.exp(-lam/h),
        tF=F*math.exp(-lam/3),y=statistics.median(costs)/2,mx=max(costs)))
for r in rows:
    pc=r['mu']/3+r['tI']+r['tC']+r['tF']; pm=r['mu']+r['tI']+r['tC']+r['tF']
    print(f"{r['name']} N={r['N']} lam={r['lam']:.2f} mu={r['mu']:.2f} I={r['I']} C={r['C']} F={r['F']:.0f} tI={r['tI']:.2f} tC={r['tC']:.2f} tF={r['tF']:.2f} pred_mu/3={pc:.2f} pred_mu={pm:.2f} meas_side_med={r['y']:.1f} ratio_mu={r['y']/pm:.2f} max_cost={r['mx']}")
y=np.array([r['y'] for r in rows])
A=np.array([[r[c] for c in ["mu","tI","tC","tF"]] for r in rows])
x,*_=np.linalg.lstsq(A[:,:3],y,rcond=None); print("lstsq a(mu),b(I),c(C) [F dropped]:",np.round(x,3))
wts=1/np.maximum(y,1); xw,*_=np.linalg.lstsq(A[:,:3]*wts[:,None],y*wts,rcond=None); print("rel-weighted [F dropped]:",np.round(xw,3))
for col,lab in [("mu","mu-term"),("mu/3","mu/3-term")]:
    B=np.array([[ (r['mu'] if col=="mu" else r['mu']/3)+r['tI']+r['tC']+r['tF'] ] for r in rows])
    k=float(((B.T@y)/(B.T@B))[0,0]); ratio=y/B[:,0]
    print(f"{lab}: single scale {k:.3f}; log-ratio sd {np.std(np.log(ratio)):.3f}")

lo=np.array([r["mu"]<=10 for r in rows]); x2,*_=np.linalg.lstsq(A[lo][:,:3],y[lo],rcond=None); print("mu<=10 subset (n=%d) a,b,c:"%lo.sum(),np.round(x2,3))
