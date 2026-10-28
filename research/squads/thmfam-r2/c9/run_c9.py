import subprocess, sys, re, os, math
W='/home/user/degree-diameter/research/squads/thmfam-r2/c9/work'
HERE='/home/user/degree-diameter/research/squads/thmfam-r2/c9'
def primes(n): return [x for x in range(2,n+1) if all(x%t for t in range(2,int(x**.5)+1))]
mode=sys.argv[1] if len(sys.argv)>1 else 'sign'
ps=[int(x) for x in sys.argv[2].split(',')] if len(sys.argv)>2 else [5,7,11]
QMAX=int(sys.argv[3]) if len(sys.argv)>3 else 100
out=open(f'{HERE}/results_{mode}.tsv','w')
out.write("p\tq\tclasses\tdistinct\tcomp\tecc_A\tecc_B\tdiam\td_A_psi_i\td_A_psi_j\td_B_psi_j\td_B_psi_k\tlog_p_q\tratio_i\n")
for p in ps:
  for q in primes(QMAX):
    if q in (2,3) or q==p: continue
    gen=subprocess.run(['python3',f'{HERE}/gen_c9.py',str(p),str(q)]+([] if mode=='sign' else ['units']),capture_output=True,text=True,cwd=W)
    info=[l for l in gen.stderr.splitlines() if l.startswith('#classes')]
    lines=[l for l in gen.stdout.splitlines() if l.strip()]
    open(f'{W}/gens_{mode}_{p}_{q}.txt','w').write("\n".join(lines)+"\n")
    cls=int(info[0].split()[1]) if info else -1
    distinct=int(info[0].split()[3]) if info else -1
    r=subprocess.run(['nice','-n','10','timeout','900',f'{HERE}/haar_dist',str(q),f'{W}/targets_{p}_{q}.txt',f'{W}/last_{mode}_{p}_{q}.txt'],input="\n".join(lines)+"\n",capture_output=True,text=True)
    res=r.stdout
    m=re.search(r'ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) compPGL=(\d+) diam=(\d+)',res)
    if not m: print("FAIL",p,q,res,r.stderr); continue
    eA,eB,cA,cB,cP,dm=map(int,m.groups())
    T=re.findall(r'TARGET (\d+) \([^)]*\) d_A=(-?\d+) d_B=(-?\d+)',res)
    dA=[int(t[1]) for t in T]; dB=[int(t[2]) for t in T]
    lg=math.log(q)/math.log(p)
    ri = dA[1]/lg if dA[1]>=0 else float('nan')
    out.write(f"{p}\t{q}\t{cls}\t{distinct}\t{cA}\t{eA}\t{eB}\t{dm}\t{dA[1]}\t{dA[2]}\t{dB[2]}\t{dB[3]}\t{lg:.3f}\t{ri:.3f}\n"); out.flush()
    print(p,q,cls,distinct,'compA',cA,'compPGL',cP,'ecc',eA,eB,'diam',dm,'dA(i)',dA[1],'dA(j)',dA[2],'dB(j)',dB[2],'dB(k)',dB[3],flush=True)
