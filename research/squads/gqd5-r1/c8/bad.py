import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from base import *
def dist_matrix(n,E):
    A=np.zeros((n,n),dtype=np.float32)
    for a,b in E: A[a,b]=A[b,a]=1
    D=np.full((n,n),-1,dtype=np.int32); np.fill_diagonal(D,0)
    reach=np.eye(n,dtype=bool); fr=reach.copy(); d=0
    while True:
        nx=((fr.astype(np.float32)@A)>0)&~reach
        if not nx.any(): break
        d+=1; D[nx]=d; reach|=nx; fr=nx
    return D
def label(v,per,np_):
    j=v//per; e=v%per
    if e<np_: k='p%d'%e
    else: k='L%d'%(e-np_)
    return 'L%d:%s'%(j,k)
if __name__=='__main__':
    q=int(sys.argv[1]) if len(sys.argv)>1 else 3
    G=getG(q); M=random_M01(G,1)
    x=0; s=G.plines[0][0]; y=[p2 for p2 in G.lines[s] if p2!=x][0]
    n,E,per=base_edges(G,M,[x,y])
    D=dist_matrix(n,E)
    bad=np.argwhere(D>5)
    print('bad ordered pairs',len(bad)//2 if False else len(bad), 'max',D.max())
    from collections import Counter
    c=Counter()
    for a,b in bad:
        if a<b: c[(a//per,b//per)]+=1
    print('by level pair (unordered):',c)
    # print a few with element labels
    for a,b in bad[:0]: pass
    # list bad pairs involving freed points
    cnt=Counter()
    for a,b in bad:
        if a<b:
            la=a%per; lb=b%per
            ta = 'pt' if la<G.np else 'ln'; tb='pt' if lb<G.np else 'ln'
            ea = la if la<G.np else -1; eb = lb if lb<G.np else -1
            cnt[(a//per,ta,b//per,tb)]+=1
    print(cnt)
    print('freed x,y=',x,y,'line s=',s, 'line of s pts', G.lines[s])
    # which pairs involve x or y
    for a,b in bad:
        if a<b and (a%per in (x,y) or b%per in (x,y)) and a//per!=b//per:
            print(label(a,per,G.np), label(b,per,G.np))
            break
