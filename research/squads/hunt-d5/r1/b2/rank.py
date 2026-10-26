rows=[]
for n in [608,616,624,625,630]:
    for line in open(f'list_{n}.txt'):
        p=line.split(None,5)
        if len(p)<6: continue
        N,i,ab=int(p[0]),int(p[1]),p[2]=='true'
        dd,zz=int(p[3]),int(p[4]); struct=p[5].strip()
        rows.append((N,i,ab,dd,zz,N//dd,struct))
keep=[r for r in rows if r[5]<=50 and r[4]<=50 and not r[2]]
print(len(rows),'total;',len(keep),'kept (G/G\'<=50, |Z|<=50, nonabelian)')
from collections import Counter
print(Counter(r[0] for r in keep))
keep.sort(key=lambda r:(r[5],r[4]))
for r in keep[:90]: print(*r[:6],r[6][:50])
