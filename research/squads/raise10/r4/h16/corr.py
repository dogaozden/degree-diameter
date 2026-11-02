import sys, statistics as st
rows=[]
for line in open(sys.argv[1]):
    p=line.split(); d={}
    d['cost']=int(p[2]); d['wmin']=int(p[4]); d['reach9']=int(p[6]); d['e4']=float(p[8]); d['dsum']=int(p[10]); d['maxfh']=int(p[12]); d['nfib']=int(p[14])
    rows.append(d)
def ranks(v):
    o=sorted(range(len(v)),key=lambda i:v[i]); r=[0]*len(v); i=0
    while i<len(v):
        j=i
        while j+1<len(v) and v[o[j+1]]==v[o[i]]: j+=1
        for k in range(i,j+1): r[o[k]]=(i+j)/2
        i=j+1
    return r
def pearson(x,y):
    mx,my=st.mean(x),st.mean(y)
    sxy=sum((a-mx)*(b-my) for a,b in zip(x,y)); sx=sum((a-mx)**2 for a in x)**.5; sy=sum((b-my)**2 for b in y)**.5
    return sxy/(sx*sy) if sx*sy>0 else float('nan')
c=[r['cost'] for r in rows]
print('n',len(rows),'cost median',st.median(c),'mean',round(st.mean(c),2),'min',min(c),'max',max(c))
for k in ['wmin','reach9','e4','dsum','maxfh','nfib']:
    x=[r[k] for r in rows]
    print(k,'pearson',round(pearson(x,c),3),'spearman',round(pearson(ranks(x),ranks(c)),3),'distinct',len(set(x)))
