import sys, subprocess, re, math
sys.path.insert(0,'/home/user/degree-diameter/research/squads/thmfam-r1/c7')
from c7lib import lines
HE='/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
def score(p,q,m,ts=None):
    L,cyc=lines(p,q,m,ts)
    r=subprocess.run([HE,'pgl',str(q),str(m)],input='\n'.join(L)+'\n',capture_output=True,text=True,timeout=900)
    mm=re.search(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
    if not mm: return None
    d,eA,eB,cA,cB,order,conn,diam=map(int,mm.groups()[:6]+(0,0)) if False else (int(mm.group(1)),int(mm.group(2)),int(mm.group(3)),int(mm.group(4)),int(mm.group(5)),int(mm.group(6)),mm.group(7),int(mm.group(8)))
    return dict(p=p,q=q,m=m,ts=ts,D=d,n=cA,nB=cB,diam=diam,conn=conn)
if __name__=='__main__':
    p,q,m=map(int,sys.argv[1:4])
    print(score(p,q,m))
