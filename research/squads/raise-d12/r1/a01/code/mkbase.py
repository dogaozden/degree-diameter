# writes base_edges.txt: first line "nb_vertices nb_edges", then "p L tree(0/1)" for each base edge (point p, line L,
# L indexed as base vertex 63+idx), spanning tree from BFS at point 0.  Also writes group tables.
import struct, sys
from collections import deque
F = '/home/user/degree-diameter/research/squads/raise-d12/r1/a01/hex/hex_q2.bin'
b = open(F,'rb').read(); q,N,L = struct.unpack('<iii', b[:12])
pts = struct.unpack('<%di' % (L*(q+1)), b[12:12+4*L*(q+1)])
n = N+L; adj=[[] for _ in range(n)]; edges=[]
for l in range(L):
    for k in range(q+1):
        p = pts[l*(q+1)+k]; edges.append((p, N+l)); adj[p].append(N+l); adj[N+l].append(p)
par=[-1]*n; seen=[False]*n; seen[0]=True; dq=deque([0]); tree=set()
while dq:
    x=dq.popleft()
    for y in adj[x]:
        if not seen[y]: seen[y]=True; tree.add((min(x,y),max(x,y))); dq.append(y)
with open('base_edges.txt','w') as f:
    f.write('%d %d\n' % (n, len(edges)))
    for p,l in edges:
        f.write('%d %d %d\n' % (p, l, 1 if (min(p,l),max(p,l)) in tree else 0))
print('edges', len(edges), 'tree', len(tree))
