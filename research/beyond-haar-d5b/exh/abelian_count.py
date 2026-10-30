# Count distinct formal products (in the free abelian group on the voltages) of the closed walks of length <= 4 at
# each base vertex of [[2,3],[3,2]] (spanning-tree voltages = 0). An abelian voltage group of order m can only work if
# every own fibre has at least m distinct formal products (coincidences can only lower the count further).
import itertools
E = [(0,2,None),(0,2,'x'),(0,3,None),(0,3,'y1'),(0,3,'y2'),(1,2,'z0'),(1,2,'z1'),(1,2,'z2'),(1,3,None),(1,3,'w')]
syms = ['x','y1','y2','z0','z1','z2','w']
def walks(start, L):
    out = set()
    def rec(v, last, depth, vec):
        if depth > 0 and v == start: out.add(tuple(vec))
        if depth == L: return
        for i,(a,b,s) in enumerate(E):
            if i == last: continue
            if a == v: to, sg = b, 1
            elif b == v: to, sg = a, -1
            else: continue
            nv = list(vec)
            if s: nv[syms.index(s)] += sg
            rec(to, i, depth+1, nv)
    rec(start, -1, 0, [0]*7)
    out.add(tuple([0]*7))
    return out
for v,name in [(0,'A0'),(1,'A1'),(2,'B0'),(3,'B1')]:
    print(name, 'distinct formal abelian products (length <= 4):', len(walks(v,4)))
