import subprocess, sys
def prim(p):
    from sympy import primitive_root
def primroot(p):
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0: fac.append(d)
        while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g
for spec in sys.argv[1:]:
    p,k,h=map(int,spec.split(','))
    g=primroot(p); r=pow(g,(p-1)//k,p)
    out=subprocess.run(['./bicos',str(p),str(k),str(h),str(r)],capture_output=True,text=True).stdout
    print(spec, out.strip().splitlines()[-1], '|', (out.strip().splitlines()[0] if len(out.strip().splitlines())>1 else ''))
