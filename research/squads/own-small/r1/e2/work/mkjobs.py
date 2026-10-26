# builds screening job list: base, group .bin, N, for every (base, N) with 508 <= b*N <= 640 (non-abelian first, cap per pair)
import glob, os, random, re
G='/home/user/degree-diameter/research/squads/own-small/r1/e2/groups'
B='/home/user/degree-diameter/research/squads/own-small/r1/e2/bases'
bases={'CAT_6':6,'CAT_8':8,'CAT_14':14,'CAT_16':16,'CAT_18':18,'CAT_20':20,'CAT_24':24,'CAT_26':26,'CAT_30':30,'CAT_32':32,'CAT_38':38}
cap=int(os.environ.get('CAP','6'))
random.seed(5)
byN={}
for info in glob.glob(G+'/g*_*.info'):
    N,gid,ab=open(info).read().split(); N=int(N); gid=int(gid.split('=')[0]) if False else int(gid)
    ab=ab.split('=')[1]=='1'
    byN.setdefault(N,[]).append((ab,gid,info[:-5]+'.bin'))
jobs=[]
for name,b in bases.items():
    for N in range(508//b+1, 640//b+1):
        if b*N<508 or b*N>640 or N not in byN: continue
        gs=byN[N]
        na=[g for g in gs if not g[0]]; ab=[g for g in gs if g[0]]
        random.shuffle(na)
        pick=na[:cap]
        if len(pick)<cap: pick+=ab[:cap-len(pick)]
        for _,gid,path in pick: jobs.append((name,b,N,gid,path))
with open('/home/user/degree-diameter/research/squads/own-small/r1/e2/work/jobs.txt','w') as o:
    for j in jobs: o.write('%s %d %d %d %s\n'%j)
print(len(jobs),'jobs'); import collections; print(collections.Counter(j[0] for j in jobs))
