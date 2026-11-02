import sys, statistics as st
exec(open('corr.py').read().split("rows=[]")[0])
rows=[]
for line in open(sys.argv[1]):
    p=line.split(); bi=p.index('S')
    B=[int(x) for x in p[1:bi]]  # B_2..B_9
    d={'cost':int(p[bi+2]),'wmin':int(p[bi+4]),'e4':float(p[bi+8]),'B':B}
    rows.append(d)
exec("def ranks"+open('corr.py').read().split("def ranks")[1].split("c=[r")[0])
c=[r['cost'] for r in rows]
print('n',len(rows),'cost median',st.median(c))
for s in range(2,10):
    x=[r['B'][s-2] for r in rows]
    print('B_%d'%s,'pearson',round(pearson(x,c),3),'spearman',round(pearson(ranks(x),ranks(c)),3),'distinct',len(set(x)))
for k in ['wmin','e4']:
    x=[r[k] for r in rows]
    print(k,'spearman',round(pearson(ranks(x),ranks(c)),3))
