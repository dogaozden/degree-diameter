import sys
# usage: mkbase.py OUT NA M   (M = multiplicity matrix rows as comma-separated string "r0;r1;..." rows of length NA)
out=sys.argv[1]; rows=[list(map(int,r.split(','))) for r in sys.argv[2].split(';')]
na=len(rows); nb=len(rows[0])
for r in rows: assert sum(r)==7 and len(r)==nb, r
for j in range(nb): assert sum(rows[i][j] for i in range(na))==7, j
E=[(i,na+j) for i in range(na) for j in range(nb) for _ in range(rows[i][j])]
with open(out,'w') as f:
    f.write("%d %d\n"%(na+nb,len(E)))
    for u,v in E: f.write("%d %d\n"%(u,v))
print(out,len(E))
