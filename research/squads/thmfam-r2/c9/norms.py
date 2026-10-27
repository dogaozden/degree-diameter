import sys, itertools, math
def elems(n):
    # all (a0,a1,a2,a3) with a0^2+a1^2+3a2^2+3a3^2 == n
    r=int(math.isqrt(n)); out=[]
    for a0 in range(-r,r+1):
        for a1 in range(-r,r+1):
            s=n-a0*a0-a1*a1
            if s<0: continue
            for a2 in range(-int(math.isqrt(s//3))-1,int(math.isqrt(s//3))+2):
                t=s-3*a2*a2
                if t<0 or t%3: continue
                u=t//3; a3=math.isqrt(u)
                if a3*a3==u:
                    out.append((a0,a1,a2,a3))
                    if a3: out.append((a0,a1,a2,-a3))
    return out
for p in [5,7,11,13,17,19,23]:
    E=elems(p); print(p,len(E),len(E)//2)
