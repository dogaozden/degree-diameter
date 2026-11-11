import sys, time, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond-small/r3/e07/pylib')
import igraph as ig
t0 = time.time()
with open('/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges') as f:
    n = int(f.readline())
    E = [tuple(map(int, l.split())) for l in f if l.strip()]
g = ig.Graph(n=n, edges=E)
print('n', g.vcount(), 'm', g.ecount(), 'deg', set(g.degree()), flush=True)
cnt = g.count_automorphisms(sh='fl')
print('count', cnt, 'time', time.time()-t0, flush=True)
gens = g.get_automorphisms_vf2 if False else None
gg = g.automorphism_group(sh='fl')
print('ngens', len(gg), 'time', time.time()-t0, flush=True)
pickle.dump(gg, open('gens.pkl', 'wb'))
