import sys,re
# usage: corrupt.py mode src dst [i j]
mode,src,dst=sys.argv[1:4]
L=open(src).read().split('\n')
def gen(i): return L[1+i]
if mode=='swapmat':      # generator i takes the (last) matrix of generator j, keeps its own z
    i,j=int(sys.argv[4]),int(sys.argv[5])
    gi=L[1+i]; gj=L[1+j]
    mj=re.search(r'(mat\([^)]*\))(?=\]| z=)',gj).group(1)
    L[1+i]=re.sub(r'(mat\([^)]*\))(?=\]? z=)',mj,gi)
elif mode=='zshift':
    i=int(sys.argv[4]); gi=L[1+i]; n=int(L[0].split()[L[0].split().index('n')+1])
    m=re.search(r'z=(\d+)',gi); L[1+i]=gi[:m.start()]+'z=%d'%((int(m.group(1))+1)%n)
elif mode=='Dminus':
    h=L[0].split(); h[1]=str(int(h[1])-1); L[0]=' '.join(h)
elif mode=='dupgen':
    L[2]=L[1].replace(L[1].split()[0],L[2].split()[0],1) if False else re.sub(r'^\d+',L[2].split()[0],L[1])
elif mode=='baddet':
    g=L[2]; m=re.search(r'mat\((\d+),(\d+),(\d+),(\d+)\)',g); a,b,c,d=map(int,m.groups())
    L[2]=g[:m.start()]+'mat(%d,%d,%d,%d)'%(a,b,c,(d+1))+g[m.end():]
elif mode=='badN':
    h=L[0].split(); k=h.index('N'); h[k+1]=str(int(h[k+1])+1); L[0]=' '.join(h)
open(dst,'w').write('\n'.join(L))
