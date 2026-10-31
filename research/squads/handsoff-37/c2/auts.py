import sys, time, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
L=open(sys.argv[1]).read().split(); n=int(L[0])
G=nx.Graph(); G.add_nodes_from(range(n))
for i in range(1,len(L),2): G.add_edge(int(L[i]),int(L[i+1]))
t=time.time(); auts=[]
gm=GraphMatcher(G,G)
for m in gm.isomorphisms_iter():
    auts.append([m[i] for i in range(n)])
    if len(auts)>5000 or time.time()-t>float(sys.argv[2]): break
print("found",len(auts),"automorphisms in",round(time.time()-t,1),"s")
import json
json.dump(auts,open(sys.argv[3],'w'))
