import re, sys, json
sys.argv=[sys.argv[0]]
exec(open('/home/user/degree-diameter/research/squads/b48/r1/c03/gen.py').read().split('out=[]')[0])
cands=[]
for N in range(1094,1201):
    for k in (6,12,24):
        if N%k: continue
        m=N//k
        for r,_ in classes(m,k):
            cands.append((N,m,k,r))
scanned=set()
for line in open('/home/user/degree-diameter/research/squads/b48/r1/scan_meta_1092_1120.txt'):
    p=line.split(); scanned.add((int(p[0])//int(p[2]),int(p[2]),int(p[3])))
new=[c for c in cands if (c[1],c[2],c[3]) not in scanned]
print('total',len(cands),'new',len(new))
K=24
step=len(new)/K
pick=[new[int(i*step)] for i in range(K)]
for p in pick: print(*p)
json.dump(pick,open('/home/user/degree-diameter/research/squads/b48/r1/c03/pick.json','w'))
