import sys; sys.path.insert(0,'.')
from hdlib import *
q=3; types='HHHDHHD'; arcs=rotational_arcs(7)
Wq,G,ovoid=setup(q)
ps=greedy_partial_spread(G)
print('ovoid',len(ovoid),'pspread',len(ps), 'valid ps', is_partial_spread(G,ps))
n,E,KB,KA=make(q,types,arcs,ovoid,ps)
print('n',n,'KB',KB,'KA',KA, 'edges', len(E))
print('bad pairs (uv>5), maxdeg-viol:', bad_pairs(n,E,5,maxdeg=q+1+3))
