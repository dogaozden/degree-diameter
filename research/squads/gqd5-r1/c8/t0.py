import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from base import *
import subprocess, time
APSP='/home/user/degree-diameter/research/theorems/d5gq/apsp'
for q in (3,5):
    G=getG(q)
    M=random_M01(G,1)
    n,E,per=base_edges(G,M,[])
    t=time.time(); print('q',q,'no freed: numpy diam',diam_numpy(n,E),'time',round(time.time()-t,2))
    p='/home/user/degree-diameter/research/squads/gqd5-r1/c8/tmp_base%d.txt'%q
    write(p,n,E)
    print(subprocess.run([APSP,p,str(q+2),'5'],capture_output=True,text=True).stdout.strip())
    # collinear pair freed
    x=0; s=G.plines[0][0]; y=[p2 for p2 in G.lines[s] if p2!=x][0]
    n,E,per=base_edges(G,M,[x,y])
    print('q',q,'R={x,y} collinear: numpy diam',diam_numpy(n,E))
    write(p,n,E)
    print(subprocess.run([APSP,p,str(q+2),'5'],capture_output=True,text=True).stdout.strip())
