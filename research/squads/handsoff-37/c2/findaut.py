"""Find colour-preserving automorphisms sigma with sigma(v0)=w for a few w (VF2 with one special vertex each)."""
import sys, json, time, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
L=open(sys.argv[1]).read().split(); n=int(L[0])
E=[(int(L[i]),int(L[i+1])) for i in range(1,len(L),2)]
v0=int(sys.argv[2]); ws=[int(x) for x in sys.argv[3].split(',')]; tl=float(sys.argv[4]); outf=sys.argv[5]
G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
found=[]
for w in ws:
    G1=G.copy(); G2=G.copy()
    for v in G1.nodes: G1.nodes[v]['c']='x'; G2.nodes[v]['c']='x'
    G1.nodes[v0]['c']='s'; G2.nodes[w]['c']='s'
    gm=GraphMatcher(G1,G2,node_match=lambda a,b: a['c']==b['c'])
    t=time.time()
    # iterate with a time limit
    for m in gm.isomorphisms_iter():
        found.append([m[i] for i in range(n)]); break
    print("w",w,"found" if found and found[-1] else "none", round(time.time()-t,2),"s", flush=True)
json.dump(found,open(outf,'w'))
print("saved",len(found))
