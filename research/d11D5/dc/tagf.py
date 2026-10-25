import sys, json, ast
from collections import Counter
base, ff = sys.argv[1], sys.argv[2]
t=open(base).read().split(); n,dg=int(t[0]),int(t[1])
ln=[sorted(int(x) for x in t[2+l*dg:2+l*dg+dg]) for l in range(n)]
W=json.load(open('/home/user/degree-diameter/research/d11D5/w8.json')); L=W['lines']
swl=set(l for l in range(585) if ln[l]!=sorted(L[l]))
newl=set(range(585,n)); newp=set(range(585,n))
pi=set(p for l in newl for p in ln[l] if p<585)
def tag(v):
    if v<n:
        if v in newp: return 'x*'
        if v in pi: return 'p_i'
        if any(v in ln[l] for l in swl): return 'onLi'
        return 'P'
    l=v-n
    if l in newl: return 'l*'
    if l in swl: return 'L_i'
    if any(p in pi for p in ln[l]): return 'thru_p'
    return 'L'
fails=[ast.literal_eval(l.replace('np.int64','')) for l in open(ff) if l.startswith('(') and l.count('(')>=2 and not l.strip()[-1].isdigit()]
c=Counter((f[2][0], tag(f[0]), tag(f[1])) for f in fails)
for k,v in c.most_common(40): print(k,v)
