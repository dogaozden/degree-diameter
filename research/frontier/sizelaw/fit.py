import math, numpy as np, csv, sys
from data import *
rows=sols()
best={}
for r in rows:
    k=(r['d'],r['D'])
    if k not in best or r['N']>best[k]['N']: best[k]=r
for r in rows:
    d,D,N=r['d'],r['D'],r['N']
    r['C']=N/(d-1)**(D-2); r['Nh']=Nh(d,D); r['kappa']=N/r['Nh']; r['mu']=mu(d,D,N)
    r['moore_frac']=2*N/moore(d,D); r['W']=W(d,D); r['WoverN']=W(d,D)/N
    r['is_best']=best[(d,D)] is r
def stats(v):
    v=np.log(np.array(v)); m=v.mean(); s=v.std(ddof=1) if len(v)>1 else float('nan')
    return math.exp(m), s, s/math.sqrt(len(v)) if len(v)>1 else float('nan')
print("== per-D constants, all files / best per cell ==")
for D in (5,8,9,10):
    for lab,sel in (('all',[r for r in rows if r['D']==D]),('best',[r for r in rows if r['D']==D and r['is_best']])):
        out=[]
        for key in ('C','kappa','mu','moore_frac'):
            g,s,se=stats([r[key] for r in sel]); out.append('%s=%.3f (sd %.1f%%, se %.1f%%)'%(key,g,100*s,100*se))
        print(D,lab,len(sel),' '.join(out))
print("== slope of log N vs log(d-1) per D (best per cell), bootstrap se ==")
rng=np.random.default_rng(1)
for D in (5,8,9,10):
    sel=[r for r in rows if r['D']==D and r['is_best']]
    x=np.log([r['d']-1 for r in sel]); y=np.log([r['N'] for r in sel])
    b=np.polyfit(x,y,1)[0]; bs=[]
    for _ in range(2000):
        i=rng.integers(0,len(x),len(x))
        if len(set(x[i]))<2: continue
        bs.append(np.polyfit(x[i],y[i],1)[0])
    # same slope for the model kappa*N_h and mu* model
    yh=np.log([r['Nh'] for r in sel]); bh=np.polyfit(x,yh,1)[0]
    print(D,'cells',len(sel),'slope %.2f +- %.2f  (D-2=%d, D-1=%d); slope of N_h itself %.2f'%(b,np.std(bs),D-2,D-1,bh))
print("== global log-residual scatter of competing laws (best per cell) ==")
B=[r for r in rows if r['is_best']]
def resid(pred):
    e=np.log([r['N']/pred(r) for r in B]); return e
laws={
 'C_D (d-1)^(D-2), C per D': None,
 'kappa*N_h, one kappa': lambda r: r['Nh'],
 'W/ln N, one const': lambda r: r['W']/math.log(r['N']),
 'N e^{-W/N}=mu*, one mu*': None,
 'Moore fraction, one const': lambda r: moore(r['d'],r['D'])/2,
 '(d-1)^(D-1), one const': lambda r: (r['d']-1)**(r['D']-1),
}
for name,f in laws.items():
    if name.startswith('C_D'):
        e=np.concatenate([np.log([r['C'] for r in B if r['D']==D])-np.log([r['C'] for r in B if r['D']==D]).mean() for D in (5,8,9,10)])
        npar=4
    elif name.startswith('N e'):
        # fit log mu*: residual in log N
        lm=np.mean(np.log([r['mu'] for r in B])); m=math.exp(lm)
        e=np.log([r['N']/Nmu(r['d'],r['D'],m) for r in B]); print('   fitted mu* = %.1f'%m); npar=1
    else:
        e=resid(f); e=e-e.mean(); npar=1
    print('%-32s rms log-resid %.3f  max |resid| %.3f  (params %d)'%(name,np.sqrt((e**2).mean()),abs(e).max(),npar))
print("== per-D fit of mu*, and per-D kappa ==")
for D in (5,8,9,10):
    sel=[r for r in B if r['D']==D]
    g,s,se=stats([r['mu'] for r in sel]); k=stats([r['kappa'] for r in sel])
    print(D,'mu* %.1f (sd of ln %.2f)'%(g,s),' kappa %.3f sd %.1f%%'%(k[0],100*k[1]))
with open('size_law_fits.csv','w',newline='') as fh:
    w=csv.writer(fh); w.writerow(['kind','degree','diameter','N_side','vertices','group','source','is_cell_best','C=N/(d-1)^(D-2)','N_h','N/N_h','W','W/N','mu=N*exp(-W/N)','2N/Moore','best_uncovered'])
    for r in sorted(rows,key=lambda r:(r['D'],r['d'],-r['N'])):
        w.writerow(['solution',r['d'],r['D'],r['N'],2*r['N'],r['spec'],r['src'],int(r['is_best']),'%.4f'%r['C'],int(r['Nh']),'%.4f'%r['kappa'],r['W'],'%.3f'%r['WoverN'],'%.2f'%r['mu'],'%.4f'%r['moore_frac'],0])
    for d,D,N,u in WALLS:
        bc=best.get((d,D)); later = bc is not None and bc['N']>=N
        w.writerow(['wall(unsolved; cell best now above)' if later else 'wall(unsolved)',d,D,N,2*N,'','HAAR_GEN_NOTES.md / d5/REPORT.md','', '%.4f'%(N/(d-1)**(D-2)),int(Nh(d,D)),'%.4f'%(N/Nh(d,D)),W(d,D),'%.3f'%(W(d,D)/N),'%.2f'%mu(d,D,N),'%.4f'%(2*N/moore(d,D)),'' if u is None else u])
print("== table of best per cell ==")
for r in sorted(B,key=lambda r:(r['D'],r['d'])):
    print('(%d,%d) N=%d C=%.3f N/Nh=%.3f W/N=%.2f mu=%.1f lnN=%.2f  %s'%(r['d'],r['D'],r['N'],r['C'],r['kappa'],r['WoverN'],r['mu'],math.log(r['N']),r['spec']))
print("== walls ==")
for d,D,N,u in WALLS: print('(%d,%d) N=%d unc=%s C=%.3f N/Nh=%.3f mu=%.1f'%(d,D,N,u,N/(d-1)**(D-2),N/Nh(d,D),mu(d,D,N)))
