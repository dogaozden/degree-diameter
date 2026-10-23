import csv, json, math, glob, os, re
from data import *
a,b,sd=4.335,-0.123,0.196
def Np(d,D,shift=0.0):
    w=W(d,D); lo,hi=10.0,float(w)
    for _ in range(200):
        m=(lo+hi)/2
        if math.log(m)-w/m < a+b*math.log(m)+shift: lo=m
        else: hi=m
    return lo
P=json.load(open('pred.json'))
rows=list(csv.reader(open('size_law_fits.csv')))
hdr=rows[0]
out=[hdr+['predicted_vertices','pred_lo_2sd','pred_hi_2sd','table','status_note']]
for r in rows[1:]: out.append(r+['','','','',''])
# this session's big-cell runs
runs=[]
for f in sorted(glob.glob('big/*.log')):
    t=open(f).read()
    m=re.search(r'RESULT d=(\d+) D=(\d+) group=(.*) N=(\d+) best=(\d+) evals=(\d+) time=([\d.]+)',t)
    if not m: continue
    d,D,g,N,best,ev,tm=int(m[1]),int(m[2]),m[3],int(m[4]),int(m[5]),int(m[6]),float(m[7])
    runs.append((d,D,g,N,best,ev,tm,os.path.basename(f)))
for d,D,g,N,best,ev,tm,lf in runs:
    kind='new-cell solution (this session, not harvested)' if best==0 else 'new-cell run, unsolved (this session)'
    out.append([kind,d,D,N,2*N,g,'big/'+lf,'','%.4f'%(N/(d-1)**(D-2)),int(Nh(d,D)),'%.4f'%(N/Nh(d,D)),W(d,D),'%.3f'%(W(d,D)/N),'%.2f'%mu(d,D,N),'%.4f'%(2*N/moore(d,D)),best,'','','','','evals=%d time=%.0fs'%(ev,tm)])
for o in P:
    d,D=o['d'],o['D']
    out.append(['prediction',d,D,int(Np(d,D)),2*int(Np(d,D)),'','mu-law ln mu*=4.335-0.123 ln N','','%.4f'%(Np(d,D)/(d-1)**(D-2)),int(Nh(d,D)),'%.4f'%(Np(d,D)/Nh(d,D)),W(d,D),'','','','',
                2*int(Np(d,D)),2*int(Np(d,D,-2*sd)),2*int(Np(d,D,2*sd)),o['table'] or '', 'model invalid (pred >= 0.95 N_h)' if Np(d,D)>=0.95*Nh(d,D) else ''])
csv.writer(open('size_law_fits_full.csv','w',newline='')).writerows(out)
print(len(out),'rows')
