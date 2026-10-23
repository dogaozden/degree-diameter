"""Plan haar_gen3 jobs by mu (SIZE_LAW.md §8).
usage: python3 plan_mu.py d D LO HI SECS [--seed S] [--slack X] [--max K] [--nmax n] [--fam sl,psl,pgl,prod (add agl1, meta)]
Lists candidate groups with order N in [LO, HI], computes mu(N) = N exp(-W/N) and the budget
M = SECS / t_eval (t_eval ~ c * N * nBFS, c = 1.5e-9 s for N >= 1e7, 4.5e-10 s below), and mu_max = max(13 + 2 ln(M/1e5), mu*(N) = exp(4.335 - 0.123 ln N)): the first rule is calibrated on long
runs at small N, the second on 10-40 minute runs at N >= 1e6 (SL(2,q) x small Z_n).
Keeps groups with mu <= mu_max + slack (default 1), sorted by N descending (biggest first), and prints job lines
'd D SECS SEED 8 GROUP... n' with a comment column. Lines go to stdout; '#' lines are ignored by batch.sh."""
import sys, math, subprocess, os
here=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,here)
from data import W, Nh
a=sys.argv[1:]
d,D,lo,hi,secs=int(a[0]),int(a[1]),int(a[2]),int(a[3]),int(a[4])
opt=dict(seed='1',slack='1',max='64',fam='sl,psl,pgl,prod',nmax='40')
for i,x in enumerate(a):
    if x.startswith('--'): opt[x[2:]]=a[i+1]
fams=opt['fam'].split(',')
src='small_cands.py' if 'meta' in fams and hi<200000 else 'cands_gen.py'
out=subprocess.run(['python3',os.path.join(here,src),str(lo),str(hi)],capture_output=True,text=True,cwd=here).stdout
rows=[]
for l in out.splitlines():
    spec,N=l.split('|'); N=int(N)
    if spec.split()[0] not in fams or int(spec.split()[-1])>int(opt['nmax']): continue
    w=W(d,D); mu=N*math.exp(-w/N); nb=1 if D%2==0 else 2
    c=1.5e-9 if N>=1e7 else 4.5e-10
    M=secs/(c*N*nb); mmax=max(13+2*math.log(M/1e5), math.exp(4.335-0.123*math.log(N)))
    if mu<=mmax+float(opt['slack']): rows.append((N,spec,mu,mmax))
rows.sort(key=lambda r:-r[0])
for N,spec,mu,mmax in rows[:int(opt['max'])]:
    print('%d %d %d %s 8 %s   # N=%d N/N_h=%.3f mu=%.1f mu_max=%.1f'%(d,D,secs,opt['seed'],spec,N,N/Nh(d,D),mu,mmax))
