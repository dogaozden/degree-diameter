import sys,time; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from sa import *
G=getG(3); M=random_M01(G,1)
R=[0,1]
n0,E,per=base_edges(G,M,R)
A0=np.zeros((n0,n0),dtype=np.float32)
for a,b in E: A0[a,b]=A0[b,a]=1
slotB={y:0 for y in R}; slotA={w:0 for w in R}; Y=[[0]]
t=time.time()
for _ in range(50):
    A=build_adj(n0,A0,R,1,1,slotB,slotA,Y); c=cost(A,3,n0,1,1)
print('per eval ms',(time.time()-t)/50*1000, c)
