import sys
def rd(f):
    t=open(f).read().split(); n,dg=int(t[0]),int(t[1])
    ln=[tuple(sorted(int(x) for x in t[2+l*dg:2+l*dg+dg])) for l in range(n)]
    return n, ln, [int(x) for x in t[2+n*dg:2+n*dg+n]]
n,l1,s1=rd(sys.argv[1]); _,l2,s2=rd(sys.argv[2])
ds=[p for p in range(n) if s1[p]!=s2[p]]; dl=[l for l in range(n) if l1[l]!=l2[l]]
print("sigma changed at", len(ds), "points; lines changed", len(dl))
if len(sys.argv)>3: print(ds); print(dl)
