import glob, os, re, math
FR = os.path.expanduser('~/AI_Projects/degree-diameter/research/frontier')
D5 = os.path.expanduser('~/AI_Projects/degree-diameter/research/d5/sols')
def W(d, D):
    if D % 2: k=(D-1)//2; return 1+sum(d*(d-1)**(2*i-1) for i in range(1,k+1))
    k=D//2; return d*sum((d-1)**(2*i) for i in range(k))
def moore(d, D): return 2*sum((d-1)**i for i in range(D))
def Nmu(d, D, mu):
    """side order N solving N exp(-W/N) = mu (largest root)"""
    w=W(d,D); lo,hi=10.0,float(w)
    for _ in range(200):
        m=(lo+hi)/2
        if m*math.exp(-w/m) < mu: lo=m
        else: hi=m
    return lo
def Nh(d, D):
    w=W(d,D); lo,hi=10.0,float(w)
    for _ in range(200):
        m=(lo+hi)/2
        if m*math.exp(-w/m) < d*math.log(m): lo=m
        else: hi=m
    return lo
def mu(d,D,N): return N*math.exp(-W(d,D)/N)
def sols():
    rows=[]
    for f in sorted(glob.glob(FR+'/sols/*.txt')):
        h=open(f).readline().split()
        d,D=int(h[0]),int(h[1]); N=int(h[h.index('N')+1]); spec=' '.join(h[2:h.index('n')])+' x Z_'+h[h.index('n')+1]
        rows.append(dict(d=d,D=D,N=N,spec=spec,src='frontier/sols/'+os.path.basename(f)))
    for f in sorted(glob.glob(D5+'/*.txt')):
        h=open(f).readline().split(); b=os.path.basename(f)
        d=int(h[0])
        if len(h)>=5: N=int(h[1]); spec=h[4].split('/')[-1][:-4]
        else: N=int(h[1])*int(h[2]); spec='meta %s %s %s'%(h[1],h[2],h[3])
        rows.append(dict(d=d,D=5,N=N,spec=spec,src='d5/sols/'+b))
    # D=5 Haar graphs documented in d5/REPORT.md but without a sols/ file
    rows.append(dict(d=5,D=5,N=176,spec='order-176 group (REPORT.md; graph 352)',src='d5/REPORT.md'))
    rows.append(dict(d=7,D=5,N=570,spec='(Z19:Z3) x Z10 (REPORT.md; graph 1140)',src='d5/REPORT.md'))
    return rows
# walls: (d, D, N, best uncovered) from HAAR_GEN_NOTES.md and d5/REPORT.md
WALLS=[(8,8,109440,1),(8,8,110880,2),(8,8,112896,2),(7,8,44310,1),(7,8,44460,1),(7,8,44640,2),(7,8,44880,3),
 (6,10,252960,2),(6,10,253080,1),(9,8,244800,1),(9,8,262080,4),(7,9,207060,2),(7,9,216000,5),(7,10,1062720,1),
 (7,10,1062936,1),(7,10,1073520,2),(8,9,619920,2),(8,9,620928,2),(8,9,622656,2),(8,9,633600,6),(8,9,655200,12),
 (9,9,1637064,4),(9,9,1642560,6),(8,10,3694968,1),(8,10,3719520,1),(10,9,3769920,2),(10,9,3801600,2),
 (9,10,11232000,2),(11,9,8265600,2),(13,8,3111552,1),(13,8,3144960,1),(13,8,3231360,4),
 (6,5,343,2),(6,5,351,2),(6,5,355,2),(8,5,882+0,None),(9,5,1378,None),(10,5,2005,8),(10,5,2016,None)]
