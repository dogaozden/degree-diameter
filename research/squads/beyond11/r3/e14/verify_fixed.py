# brute-force check of |C_SL(g)| and |{x in SL: x g x^-1 = +-g}| for g=[[0,-1],[1,-1]] at small p
import sys
def mul(a,b,p):
    return ((a[0]*b[0]+a[1]*b[2])%p,(a[0]*b[1]+a[1]*b[3])%p,(a[2]*b[0]+a[3]*b[2])%p,(a[2]*b[1]+a[3]*b[3])%p)
def inv(a,p):  # SL inverse
    return (a[3]%p,(-a[1])%p,(-a[2])%p,a[0]%p)
for p in [5,7,11,13,17,19,23,29,31]:
    g=(0,p-1,1,p-1)
    cent=0; cent_pm=0
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    if (a*d-b*c)%p!=1: continue
                    x=(a,b,c,d)
                    xg=mul(x,g,p); gx=mul(g,x,p)
                    if xg==gx: cent+=1
                    if xg==gx or xg==tuple((-t)%p for t in gx): cent_pm+=1
    eps=1 if p%3==1 else -1
    print(f"p={p} p%3={p%3} |C_SL(g)|={cent} (pred p-eps={p-(1 if p%3==1 else -1)}) |{{x: xgx^-1=+-g}}|={cent_pm} -> PSL F={cent_pm//2} (pred {(p-(1 if p%3==1 else -1))//2})")
