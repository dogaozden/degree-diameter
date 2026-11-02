import re, json, os, sys, math
from math import gcd
M='/home/user/degree-diameter/research/squads/raise9/r1/m01'
def inv(a,b,c,d,p): return (d%p,(-b)%p,(-c)%p,a%p)
def mul(X,Y,p):
    a,b,c,d=X; e,f,g,h=Y
    return ((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p)
def order_M(X,p,proj):
    I=(1,0,0,1); mI=(p-1,0,0,p-1); Y=X; k=1
    while True:
        if Y==I or (proj and Y==mI): return k
        Y=mul(Y,X,p); k+=1
        if k>4*p: return None
def classify(X,z,p,n,proj,AG,AR):
    a,b,c,d=X
    if X in [(1,0,0,1),(p-1,0,0,p-1)]: return 'central'
    oM=order_M(X,p,proj); oz = n//gcd(z,n) if n>1 else 1
    o=oM*oz//gcd(oM,oz)
    if o==2: return 'involution'
    # alpha(x) = (AG X AG^-1, AR z)
    Y=mul(mul(AG,X,p),inv(*AG,p),p)
    fixM = (Y==X) or (proj and Y==((p-X[0])%p,(p-X[1])%p,(p-X[2])%p,(p-X[3])%p))
    if fixM and (AR*z-z)%n==0: return 'alpha_fixed'
    return 'generic'
rows=[]
res=[json.loads(l) for l in open(f'{M}/results.jsonl')]
seen=set()
out=[]
for r in res:
    key=r['key']
    if key in seen: continue
    seen.add(key)
    fam,p,n=r['fam'],r['p'],r['n']
    if not r['summary']: continue
    s=r['summary']
    mm=re.search(r'min=(\d+) p10=(\d+) median=(\d+) mean=([\d.]+) mu=([\d.]+)',s)
    mn,p10,med,mean,mu=mm.groups()
    err=open(f'{M}/logs/{key}.err').read()
    ma=re.search(r'conj by mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\), z -> (\d+) z',err)
    AG=tuple(int(x)%p for x in ma.groups()[:4]); AR=int(ma.group(5))
    proj = fam=='psl'
    dump=f'{M}/unc/{key}.txt'
    cnt={'central':0,'involution':0,'alpha_fixed':0,'generic':0}
    cnt_side={0:0,1:0}; nsamp=0; tot=0
    if os.path.exists(dump):
        for line in open(dump):
            if line.startswith('SAMPLE'): nsamp+=1; continue
            if not line.startswith('U '): continue
            mt=re.search(r'mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\) z=(\d+) side (\d)',line)
            X=tuple(int(x)%p for x in mt.groups()[:4]); z=int(mt.group(5)); side=int(mt.group(6))
            cl=classify(X,z,p,n,proj,AG,AR)
            cnt[cl]+=1; cnt_side[side]+=1; tot+=1
    ns=max(nsamp,1)
    line={'key':key,'fam':fam,'p':p,'n':n,'N':None,'mu':float(mu),'samples':nsamp,'min':int(mn),'p10':int(p10),'median':int(med),'mean':float(mean),
          'per_sample':{k:round(v/ns,2) for k,v in cnt.items()},'side0_per_sample':round(cnt_side[0]/ns,2),'side1_per_sample':round(cnt_side[1]/ns,2)}
    out.append(line)
json.dump(out,open(f'{M}/classes.json','w'),indent=1)
hdr='| group | orbit | mu | min | p10 | median | mean | central/s | involution/s | alpha-fixed/s | generic/s | samples |'
print(hdr); print('|'+'---|'*12)
for l in out:
    pc=l['per_sample']; orb=l['key'].split('_k')[1]
    print(f"| {l['fam'].upper()}({l['p']}) x Z{l['n']} | {orb} | {l['mu']:.1f} | {l['min']} | {l['p10']} | {l['median']} | {l['mean']:.1f} | {pc['central']} | {pc['involution']} | {pc['alpha_fixed']} | {pc['generic']} | {l['samples']} |")
