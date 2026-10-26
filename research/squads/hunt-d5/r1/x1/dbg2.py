import sys, random
sys.argv = ['x', 'g392_5.bin', '5', '1', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
import numpy as np
a = 120; b = 303
Aid, Bid, Arep, Brep, dcs = setup(a, b)
n = len(Arep)
p4 = [i for i,d in enumerate(dcs) if len(d)==4]; p2=[i for i,d in enumerate(dcs) if len(d)==2]
r = random.Random(5)
for trial in range(6):
    st = r.sample(p4, 4) + r.sample(p2, 1) if len(p2)>=1 else r.sample(p4,5)
    Dl = [e for c in st for e in dcs[c]]
    M = adjacency(Dl, Arep, Bid)
    # components via BFS on bipartite graph
    adj = [np.nonzero(M[i])[0].tolist() for i in range(n)]
    badj = [np.nonzero(M[:,j])[0].tolist() for j in range(n)]
    seen=set(); comps=0
    for s in range(n):
        if s in seen: continue
        comps+=1; stack=[('A',s)]; seen.add(('A',s))
        while stack:
            side,v=stack.pop()
            nb = adj[v] if side=='A' else badj[v]
            for w in nb:
                key=('B' if side=='A' else 'A', w)
                if key not in seen: seen.add(key); stack.append(key)
    print(trial, 'cost', cost(M), 'components(A-rooted)', comps, 'Dsize', len(Dl), 'st', st)
print('a,b classes', dcs[:0], 'Arep[:5]', Arep[:5])
