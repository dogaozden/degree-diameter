import glob, os, sys
P='/home/user/degree-diameter/research/d11D5/plus/'
def load(fn):
    t=open(fn).read().split()
    n,dg=int(t[0]),int(t[1])
    v=list(map(int,t[2:]))
    L=[tuple(sorted(v[l*dg:(l+1)*dg])) for l in range(n)]
    s=v[n*dg:n*dg+n]
    return n,dg,L,s,v[:n*dg]
files=[f for f in sorted(glob.glob(P+'best_*.in'))]
data={}
for f in files:
    data[os.path.basename(f)]=load(f)
# group by identical line lists (as sets of lines per line index, ordered)
groups={}
for k,(n,dg,L,s,raw) in data.items():
    groups.setdefault(tuple(raw),[]).append(k)
for g,ks in groups.items():
    print(len(ks), ks)
# base comparison as unordered set of line-point sets
for k,(n,dg,L,s,raw) in data.items():
    pass
# check all pairs, number of differing lines among cost-2 candidates
c2=['best_f5.in','best_g61.in','best_h71.in','best_h72.in','best_m81.in','best_m82.in','best_m83.in','best_u602.in','best_v701.in','best_v702.in','best_y901.in']
base=data['best_y901.in'][2]
for k in c2:
    L=data[k][2]
    diff=sum(1 for a,b in zip(base,L) if a!=b)
    print(k,'lines differing from y901:',diff)
